"""Tests for the density matrix noise simulator."""

import numpy as np
import pytest
from vqt.dsl.builder import simple_circuit
from vqt.compiler.simulator import NativeSimulator
from vqt.compiler.noise import NoisySimulator, NoiseConfig, fidelity
from vqt.optimization.passes import GateCancellationPass


class TestNoisySimulator:
    def test_zero_noise_matches_ideal(self):
        """With no noise, density matrix should match |psi><psi| from statevector."""
        b = simple_circuit(2, "bell_noise")
        b.h(0)
        b.cx(0, 1)
        circuit = b.build()

        ideal_sim = NativeSimulator()
        sv = ideal_sim.run(circuit)

        noisy_sim = NoisySimulator()
        rho = noisy_sim.run(circuit, NoiseConfig(0.0, 0.0))

        # rho should equal |psi><psi|
        expected_rho = np.outer(sv, np.conj(sv))
        assert np.allclose(rho, expected_rho, atol=1e-10)

    def test_zero_noise_fidelity_one(self):
        """Fidelity should be 1.0 with zero noise."""
        b = simple_circuit(1, "h_gate")
        b.h(0)
        circuit = b.build()

        ideal_sv = NativeSimulator().run(circuit)
        rho = NoisySimulator().run(circuit, NoiseConfig(0.0, 0.0))
        f = fidelity(rho, ideal_sv)
        assert abs(f - 1.0) < 1e-10

    def test_density_matrix_trace_one(self):
        """Trace of density matrix should be 1 regardless of noise."""
        b = simple_circuit(2, "noisy_bell")
        b.h(0)
        b.cx(0, 1)
        circuit = b.build()

        rho = NoisySimulator().run(circuit, NoiseConfig(0.05, 0.02))
        assert abs(np.trace(rho).real - 1.0) < 1e-10

    def test_density_matrix_hermitian(self):
        """Density matrix should be Hermitian."""
        b = simple_circuit(2, "herm_test")
        b.h(0)
        b.cx(0, 1)
        circuit = b.build()

        rho = NoisySimulator().run(circuit, NoiseConfig(0.05, 0.02))
        assert np.allclose(rho, rho.conj().T, atol=1e-10)

    def test_density_matrix_positive_eigenvalues(self):
        """Density matrix should have non-negative eigenvalues."""
        b = simple_circuit(2, "pos_test")
        b.h(0)
        b.cx(0, 1)
        circuit = b.build()

        rho = NoisySimulator().run(circuit, NoiseConfig(0.05, 0.02))
        eigenvalues = np.linalg.eigvalsh(rho)
        assert all(ev >= -1e-10 for ev in eigenvalues)

    def test_depolarizing_reduces_fidelity(self):
        """Depolarizing noise should reduce fidelity below 1.0."""
        b = simple_circuit(1, "depol_test")
        b.h(0)
        circuit = b.build()

        ideal_sv = NativeSimulator().run(circuit)
        rho = NoisySimulator().run(circuit, NoiseConfig(depolarizing_rate=0.1))
        f = fidelity(rho, ideal_sv)
        assert f < 1.0
        assert f > 0.5  # Should still be reasonable

    def test_depolarizing_preserves_trace(self):
        """Depolarizing channel preserves trace."""
        b = simple_circuit(1, "depol_trace")
        b.x(0)
        circuit = b.build()

        rho = NoisySimulator().run(circuit, NoiseConfig(depolarizing_rate=0.2))
        assert abs(np.trace(rho).real - 1.0) < 1e-10

    def test_amplitude_damping_decays_to_ground(self):
        """Amplitude damping on |1> should produce some |0> population."""
        b = simple_circuit(1, "ad_test")
        b.x(0)  # Prepare |1>
        circuit = b.build()

        rho = NoisySimulator().run(circuit, NoiseConfig(amplitude_damping_rate=0.3))
        # |0> population should be > 0 due to damping
        assert rho[0, 0].real > 0.1

    def test_amplitude_damping_ground_state_unaffected(self):
        """Amplitude damping on |0> should not change the state."""
        b = simple_circuit(1, "ad_ground")
        # No gates — stays in |0>
        circuit = b.build()

        rho = NoisySimulator().run(circuit, NoiseConfig(amplitude_damping_rate=0.5))
        assert abs(rho[0, 0].real - 1.0) < 1e-10
        assert abs(rho[1, 1].real) < 1e-10

    def test_more_noise_lower_fidelity(self):
        """Higher noise rate should give lower fidelity."""
        b = simple_circuit(2, "noise_compare")
        b.h(0)
        b.cx(0, 1)
        circuit = b.build()

        ideal_sv = NativeSimulator().run(circuit)
        sim = NoisySimulator()

        rho_low = sim.run(circuit, NoiseConfig(depolarizing_rate=0.01))
        rho_high = sim.run(circuit, NoiseConfig(depolarizing_rate=0.1))

        f_low = fidelity(rho_low, ideal_sv)
        f_high = fidelity(rho_high, ideal_sv)
        assert f_low > f_high

    def test_optimized_better_fidelity_under_noise(self):
        """Key demo: optimized circuit should have better fidelity under noise."""
        # Original: H, CX, X, X (4 gates -> more noise)
        b = simple_circuit(2, "opt_noise")
        b.h(0)
        b.cx(0, 1)
        b.x(0)
        b.x(0)
        original = b.build()

        # Optimized: H, CX (2 gates -> less noise)
        opt = GateCancellationPass().run(original)

        ideal_sv = NativeSimulator().run(opt)
        sim = NoisySimulator()
        noise = NoiseConfig(depolarizing_rate=0.05, amplitude_damping_rate=0.02)

        rho_orig = sim.run(original, noise)
        rho_opt = sim.run(opt, noise)

        f_orig = fidelity(rho_orig, ideal_sv)
        f_opt = fidelity(rho_opt, ideal_sv)
        assert f_opt > f_orig

    def test_single_qubit_rz_with_noise(self):
        """RZ gate with noise should still produce valid density matrix."""
        import math
        b = simple_circuit(1, "rz_noise")
        b.rz(0, math.pi / 4)
        circuit = b.build()

        rho = NoisySimulator().run(circuit, NoiseConfig(0.05, 0.05))
        assert abs(np.trace(rho).real - 1.0) < 1e-10
        assert np.allclose(rho, rho.conj().T, atol=1e-10)
