# Tests du module edgar_signal.
#
# Les tests CPU ci-dessous n'utilisent PAS le reseau : ils s'appuient sur
# des fixtures inline (HTML, JSON submissions synthetiques). Le smoke test
# reseau reel (cf tests/test_smoke_sec_real.py) est volontairement separe et
# instrumente pour ne pas tourner par defaut -- acceptance #6.
