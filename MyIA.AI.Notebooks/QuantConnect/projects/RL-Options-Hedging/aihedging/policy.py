#region imports
from AlgorithmImports import *

import torch as T
import torch.nn as nn
from torch import optim
import torch.nn.functional as F
import torch.distributions as D
#endregion


class Policy(nn.Module):
    
    def __init__(self, device):
        super(Policy, self).__init__()
        # Define the network layers.
        self._fcin = nn.Linear(3, 256)
        self._fc1 = nn.Linear(256, 256)
        self._fcout = nn.Linear(256, 1*2)
        # Define the optimizer.
        self.optimizer = optim.Adam(self.parameters(), lr=3e-4)
        # Move the network's parameters and buffers to the correct 
        # device (CPU or GPU).
        self.to(T.device(device))

    def forward(self, state):
        x = F.relu(self._fcin(state))
        x = F.relu(self._fc1(x))
        x = self._fcout(x)
        lmu, lsig = x.split(1,dim=-1)
        return F.sigmoid(lmu), F.sigmoid(lsig)+1e-12

    def sample(self, state):
        mu, sig = self.forward(state)
        d = D.normal.Normal(mu, sig)
        sample = d.rsample()
        return sample, d.log_prob(sample).sum(axis=-1)


