"""Custom Pythae training callbacks for benchmark metrics."""

from __future__ import annotations

import time
from collections import defaultdict

import torch
from pythae.trainers.training_callbacks import TrainingCallback


class TimingCallback(TrainingCallback):
    """Records per-step wall-clock time with proper CUDA synchronization."""

    def __init__(self):
        self.step_times: list[float] = []
        self._t0: float = 0.0

    def on_train_step_begin(self, training_config, **kwargs):
        if torch.cuda.is_available():
            torch.cuda.synchronize()
        self._t0 = time.perf_counter()

    def on_train_step_end(self, training_config, **kwargs):
        if torch.cuda.is_available():
            torch.cuda.synchronize()
        self.step_times.append(time.perf_counter() - self._t0)

    @property
    def mean_step_ms(self) -> float:
        if not self.step_times:
            return 0.0
        return 1000.0 * sum(self.step_times) / len(self.step_times)

    @property
    def epoch_step_times_ms(self) -> list[float]:
        return [t * 1000.0 for t in self.step_times]


class MemoryCallback(TrainingCallback):
    """Tracks peak GPU memory during training."""

    def __init__(self):
        self.peak_memory_mb: float = 0.0

    def on_train_begin(self, training_config, **kwargs):
        if torch.cuda.is_available():
            torch.cuda.reset_peak_memory_stats()

    def on_train_end(self, training_config, **kwargs):
        if torch.cuda.is_available():
            self.peak_memory_mb = torch.cuda.max_memory_allocated() / (1024 ** 2)


class EpochMetricsCallback(TrainingCallback):
    """Collects per-epoch train/eval loss for later analysis."""

    def __init__(self):
        self.train_losses: list[float] = []
        self.eval_losses: list[float] = []

    def on_log(self, training_config, logs=None, **kwargs):
        if logs is None:
            return
        if "train_epoch_loss" in logs:
            self.train_losses.append(float(logs["train_epoch_loss"]))
        if "eval_epoch_loss" in logs:
            self.eval_losses.append(float(logs["eval_epoch_loss"]))
