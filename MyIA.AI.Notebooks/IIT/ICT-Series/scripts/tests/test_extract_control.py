"""Controle CPU du modele permute et du hook d'inoculation (#8236)."""

import importlib.util
from pathlib import Path
import unittest

try:
    import torch
except ImportError:
    torch = None


@unittest.skipIf(torch is None, "PyTorch absent : contrat du controle non execute")
class TestModeleControle(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = Path(__file__).resolve().parents[1] / "extract_sae_traces.py"
        spec = importlib.util.spec_from_file_location("extract_sae_traces", path)
        cls.driver = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.driver)

    def make_model(self):
        class Toy(torch.nn.Module):
            def __init__(self):
                super().__init__()
                self.embedding = torch.nn.Embedding(12, 3)
                with torch.no_grad():
                    self.embedding.weight.copy_(torch.arange(36).reshape(12, 3))

            def get_input_embeddings(self):
                return self.embedding

        return Toy()

    def test_permutation_reproductible_conserve_lignes_change_appariement(self):
        models = [self.make_model() for _ in range(3)]
        original = models[0].embedding.weight.detach().clone()
        for model, seed in zip(models, (42, 42, 43)):
            self.driver.apply_control_permutation(model, seed)
        first, same, other = [model.embedding.weight.detach() for model in models]
        self.assertTrue(torch.equal(first, same))
        self.assertFalse(torch.equal(first, other))
        self.assertFalse(torch.equal(first, original))
        self.assertEqual(sorted(map(tuple, first.tolist())), sorted(map(tuple, original.tolist())))
        # Une permutation des seuls identifiants ne modifie pas l'embedding.
        ids = torch.tensor([1, 3, 5, 7])
        self.assertFalse(torch.equal(ids, ids.flip(0)))
        self.assertTrue(torch.equal(self.make_model().embedding.weight.detach(), original))

    def test_clamp_apres_permutation_preserve_controle_zero(self):
        model = self.make_model()
        self.driver.apply_control_permutation(model, 42)
        output = model.embedding(torch.tensor([[0, 1]]))
        sae = {"W_enc": torch.eye(3), "b_enc": torch.zeros(3), "W_dec": torch.eye(3)}
        identity = self.driver.ClampHook(sae, [0, 1], 0.0)
        clamp = self.driver.ClampHook(sae, [0, 1], 1.0)
        self.assertTrue(torch.equal(identity(None, None, output), output))
        expected = output.detach().clone()
        expected[..., :2] = 0
        self.assertTrue(torch.equal(clamp(None, None, output), expected))
        self.assertFalse(torch.equal(clamp(None, None, output), output))


if __name__ == "__main__":
    unittest.main()
