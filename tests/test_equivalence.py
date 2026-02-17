import numpy as np
import pytest
from vqt.dsl.builder import simple_circuit
from vqt.certification.equivalence import EquivalenceChecker
from vqt.compiler.simulator import NativeSimulator

sim = NativeSimulator()
checker = EquivalenceChecker()


class TestEquivalence:
    def test_same_circuit_fidelity_one(self):
        b = simple_circuit(2, "bell")
        b.h(0)
        b.cx(0, 1)
        circuit = b.build()
        sv = sim.run(circuit)
        report = checker.check(circuit, sv, "test")
        assert report.is_equivalent
        assert np.isclose(report.fidelity, 1.0)

    def test_different_circuit_fidelity_below_one(self):
        b1 = simple_circuit(1, "a")
        b1.h(0)
        c1 = b1.build()

        b2 = simple_circuit(1, "b")
        b2.x(0)
        c2 = b2.build()

        sv2 = sim.run(c2)
        report = checker.check(c1, sv2, "test")
        assert not report.is_equivalent
        assert report.fidelity < 1.0
