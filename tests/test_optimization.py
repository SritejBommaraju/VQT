import numpy as np
import pytest
from vqt.dsl.builder import simple_circuit
from vqt.optimization.passes import (
    GateCancellationPass,
    IdentityRemovalPass,
    CommuteThenCancelPass,
)
from vqt.compiler.simulator import NativeSimulator

sim = NativeSimulator()


class TestGateCancellation:
    def test_removes_adjacent_x_pair(self):
        b = simple_circuit(1, "cancel")
        b.h(0)
        b.x(0)
        b.x(0)
        circuit = b.build()
        opt = GateCancellationPass().run(circuit)
        assert opt.gate_count == 1  # only H remains

    def test_preserves_semantics(self):
        b = simple_circuit(2, "sem")
        b.h(0)
        b.cx(0, 1)
        b.x(0)
        b.x(0)
        circuit = b.build()
        sv_before = sim.run(circuit)

        opt = GateCancellationPass().run(circuit)
        sv_after = sim.run(opt)
        assert np.allclose(sv_before, sv_after)

    def test_no_op_when_nothing_to_cancel(self):
        b = simple_circuit(1, "noop")
        b.h(0)
        b.x(0)
        circuit = b.build()
        opt = GateCancellationPass().run(circuit)
        assert opt.gate_count == 2


class TestIdentityRemoval:
    def test_removes_rz_zero(self):
        b = simple_circuit(1, "idr")
        b.h(0)
        b.rz(0, 0.0)
        circuit = b.build()
        opt = IdentityRemovalPass().run(circuit)
        assert opt.gate_count == 1

    def test_keeps_nonzero_rz(self):
        b = simple_circuit(1, "idr2")
        b.rz(0, 1.5)
        circuit = b.build()
        opt = IdentityRemovalPass().run(circuit)
        assert opt.gate_count == 1


class TestCommuteThenCancel:
    def test_commute_disjoint_then_cancel(self):
        """Z(0), X(1), Z(0) — X(1) commutes past Z(0) since disjoint, then Z*Z cancels."""
        b = simple_circuit(2, "commute")
        b.z(0)
        b.x(1)
        b.z(0)
        circuit = b.build()
        opt = CommuteThenCancelPass().run(circuit)
        # Z pair cancelled, only X(1) remains
        assert opt.gate_count == 1

    def test_preserves_semantics_commute(self):
        b = simple_circuit(2, "csem")
        b.z(0)
        b.x(1)
        b.z(0)
        circuit = b.build()
        sv_before = sim.run(circuit)
        opt = CommuteThenCancelPass().run(circuit)
        sv_after = sim.run(opt)
        assert np.allclose(sv_before, sv_after)
