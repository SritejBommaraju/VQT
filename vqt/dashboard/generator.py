"""HTML certificate dashboard and ASCII circuit diagram generator."""

import html
from typing import Dict, Any, Optional, List
from vqt.core.ir import QuantumCircuit


def circuit_to_ascii(circuit: QuantumCircuit) -> str:
    """Generate an ASCII art circuit diagram."""
    n = circuit.num_qubits
    if n == 0:
        return "(empty circuit)"

    # Build columns for each instruction
    columns: List[List[str]] = []
    for instr in circuit.instructions:
        gate_name = instr.gate.name.lower()
        targets = [q.index for q in instr.qubits]
        col = ['---'] * n

        if gate_name == 'cx' and len(targets) == 2:
            ctrl, tgt = targets
            col[ctrl] = '-*-'
            col[tgt] = '-X-'
            # Draw vertical wire between control and target
            lo, hi = min(ctrl, tgt), max(ctrl, tgt)
            for i in range(lo + 1, hi):
                if col[i] == '---':
                    col[i] = '-|-'
        elif gate_name == 'swap' and len(targets) == 2:
            a, b = targets
            col[a] = '-X-'
            col[b] = '-X-'
            lo, hi = min(a, b), max(a, b)
            for i in range(lo + 1, hi):
                if col[i] == '---':
                    col[i] = '-|-'
        elif gate_name == 'measure':
            col[targets[0]] = '-M-'
        elif instr.gate.params:
            label = f'{gate_name.upper()}({instr.gate.params[0]:.2f})'
            padded = f'-{label}-'
            col[targets[0]] = padded
        else:
            label = gate_name.upper()
            col[targets[0]] = f'-{label}-'

        columns.append(col)

    if not columns:
        # No instructions — just wires
        lines = []
        for i in range(n):
            reg_name = circuit.qregs[0].name if circuit.qregs else 'q'
            lines.append(f'{reg_name}[{i}] : ---')
        return '\n'.join(lines)

    # Normalize column widths
    col_widths = []
    for col in columns:
        col_widths.append(max(len(cell) for cell in col))

    # Build output
    lines = []
    for i in range(n):
        reg_name = circuit.qregs[0].name if circuit.qregs else 'q'
        prefix = f'{reg_name}[{i}] : '
        wire = ''
        for ci, col in enumerate(columns):
            cell = col[i]
            w = col_widths[ci]
            # Pad with dashes to align
            pad = w - len(cell)
            left_pad = pad // 2
            right_pad = pad - left_pad
            wire += '-' * left_pad + cell + '-' * right_pad
        lines.append(prefix + wire + '---')
    return '\n'.join(lines)


def _generate_svg_bar_chart(orig_counts: Dict[str, int],
                            opt_counts: Dict[str, int]) -> str:
    """Generate an inline SVG bar chart comparing gate counts."""
    all_gates = sorted(set(list(orig_counts.keys()) + list(opt_counts.keys())))
    if not all_gates:
        return '<p>No gates to display.</p>'

    bar_width = 30
    gap = 10
    group_width = bar_width * 2 + gap
    chart_width = len(all_gates) * (group_width + 20) + 60
    max_count = max(max(orig_counts.values(), default=1), max(opt_counts.values(), default=1))
    chart_height = 200
    scale = (chart_height - 40) / max(max_count, 1)

    svg = f'<svg width="{chart_width}" height="{chart_height + 40}" xmlns="http://www.w3.org/2000/svg">\n'
    svg += f'  <rect width="{chart_width}" height="{chart_height + 40}" fill="#1a1a2e" rx="8"/>\n'

    x = 40
    for gate in all_gates:
        orig_val = orig_counts.get(gate, 0)
        opt_val = opt_counts.get(gate, 0)

        orig_h = orig_val * scale
        opt_h = opt_val * scale

        y_base = chart_height - 10

        # Original bar
        svg += f'  <rect x="{x}" y="{y_base - orig_h}" width="{bar_width}" height="{orig_h}" fill="#e94560" rx="2"/>\n'
        if orig_val > 0:
            svg += f'  <text x="{x + bar_width // 2}" y="{y_base - orig_h - 4}" text-anchor="middle" fill="#e94560" font-size="11">{orig_val}</text>\n'

        # Optimized bar
        svg += f'  <rect x="{x + bar_width + gap}" y="{y_base - opt_h}" width="{bar_width}" height="{opt_h}" fill="#0f3460" rx="2"/>\n'
        if opt_val > 0:
            svg += f'  <text x="{x + bar_width + gap + bar_width // 2}" y="{y_base - opt_h - 4}" text-anchor="middle" fill="#0f3460" font-size="11">{opt_val}</text>\n'

        # Label
        svg += f'  <text x="{x + (group_width) // 2}" y="{y_base + 16}" text-anchor="middle" fill="#aaa" font-size="11">{html.escape(gate.upper())}</text>\n'
        x += group_width + 20

    # Legend
    lx = chart_width - 160
    svg += f'  <rect x="{lx}" y="8" width="12" height="12" fill="#e94560" rx="2"/>\n'
    svg += f'  <text x="{lx + 16}" y="18" fill="#ccc" font-size="11">Original</text>\n'
    svg += f'  <rect x="{lx + 80}" y="8" width="12" height="12" fill="#0f3460" rx="2"/>\n'
    svg += f'  <text x="{lx + 96}" y="18" fill="#ccc" font-size="11">Optimized</text>\n'

    svg += '</svg>'
    return svg


def _generate_hash_chain_svg(orig_hash: str, opt_hash: str,
                              results_hash: str) -> str:
    """Generate an SVG showing the hash chain flow."""
    svg = '<svg width="700" height="80" xmlns="http://www.w3.org/2000/svg">\n'
    svg += '  <rect width="700" height="80" fill="#1a1a2e" rx="8"/>\n'

    # Three boxes with arrows
    boxes = [
        (10, f'Original: {orig_hash[:12]}...'),
        (250, f'Optimized: {opt_hash[:12]}...'),
        (490, f'Results: {results_hash[:12]}...'),
    ]
    for bx, label in boxes:
        svg += f'  <rect x="{bx}" y="25" width="190" height="30" fill="#16213e" stroke="#0f3460" rx="4"/>\n'
        svg += f'  <text x="{bx + 95}" y="45" text-anchor="middle" fill="#e0e0e0" font-size="10">{html.escape(label)}</text>\n'

    # Arrows
    for ax in [200, 440]:
        svg += f'  <line x1="{ax}" y1="40" x2="{ax + 50}" y2="40" stroke="#e94560" stroke-width="2" marker-end="url(#arrowhead)"/>\n'

    svg += '  <defs><marker id="arrowhead" markerWidth="10" markerHeight="7" refX="10" refY="3.5" orient="auto">'
    svg += '<polygon points="0 0, 10 3.5, 0 7" fill="#e94560"/></marker></defs>\n'
    svg += '</svg>'
    return svg


def generate_dashboard(
    original_circuit: QuantumCircuit,
    optimized_circuit: QuantumCircuit,
    opt_trace: Any,
    equiv_report: Any,
    certificate: Any,
    signature_envelope: Optional[Dict[str, Any]] = None,
    signature_valid: Optional[bool] = None,
) -> str:
    """Generate a self-contained HTML dashboard for a VQT certification run."""

    orig_ascii = html.escape(circuit_to_ascii(original_circuit))
    opt_ascii = html.escape(circuit_to_ascii(optimized_circuit))

    orig_counts = original_circuit.gate_count_by_type()
    opt_counts = optimized_circuit.gate_count_by_type()
    bar_chart_svg = _generate_svg_bar_chart(orig_counts, opt_counts)

    orig_hash = html.escape(certificate.original_ir_hash)
    opt_hash = html.escape(certificate.optimized_ir_hash)
    results_hash = html.escape(certificate.results_hash)
    hash_chain_svg = _generate_hash_chain_svg(orig_hash, opt_hash, results_hash)

    fidelity_val = equiv_report.fidelity
    fidelity_class = 'pass' if equiv_report.is_equivalent else 'fail'
    fidelity_label = 'PASS' if equiv_report.is_equivalent else 'FAIL'

    cert_hash = html.escape(certificate.digest()[:32] + '...')
    circuit_name = html.escape(certificate.circuit_name)

    sig_status = ''
    if signature_valid is not None:
        if signature_valid:
            sig_status = '<span class="sig-valid">SIGNATURE VALID</span>'
        else:
            sig_status = '<span class="sig-invalid">SIGNATURE INVALID</span>'

    # Optimization steps summary
    opt_steps_html = ''
    if opt_trace and hasattr(opt_trace, 'steps'):
        for step in opt_trace.steps:
            step_name = html.escape(step.pass_name)
            n_transforms = len(step.transformations)
            opt_steps_html += f'<li><strong>{step_name}</strong>: {n_transforms} transformation(s)</li>\n'

    return f'''<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>VQT Certificate Dashboard - {circuit_name}</title>
<style>
  * {{ margin: 0; padding: 0; box-sizing: border-box; }}
  body {{ font-family: 'Segoe UI', system-ui, sans-serif; background: #0d1117; color: #e0e0e0; padding: 20px; }}
  .container {{ max-width: 1000px; margin: 0 auto; }}
  h1 {{ color: #58a6ff; margin-bottom: 8px; }}
  h2 {{ color: #79c0ff; margin: 24px 0 12px 0; border-bottom: 1px solid #21262d; padding-bottom: 6px; }}
  .header {{ text-align: center; padding: 20px 0; }}
  .header .subtitle {{ color: #8b949e; }}
  .grid {{ display: grid; grid-template-columns: 1fr 1fr; gap: 16px; }}
  .card {{ background: #161b22; border: 1px solid #30363d; border-radius: 8px; padding: 16px; }}
  .card h3 {{ color: #58a6ff; margin-bottom: 8px; font-size: 14px; text-transform: uppercase; letter-spacing: 1px; }}
  pre {{ background: #0d1117; border: 1px solid #21262d; border-radius: 6px; padding: 12px; overflow-x: auto; font-size: 12px; line-height: 1.5; color: #c9d1d9; }}
  .fidelity-badge {{ display: inline-block; padding: 6px 20px; border-radius: 20px; font-weight: bold; font-size: 18px; }}
  .fidelity-badge.pass {{ background: #238636; color: #fff; }}
  .fidelity-badge.fail {{ background: #da3633; color: #fff; }}
  .certified-stamp {{ text-align: center; margin: 20px 0; padding: 20px; border: 3px solid #238636; border-radius: 12px; background: rgba(35, 134, 54, 0.1); }}
  .certified-stamp .label {{ font-size: 28px; font-weight: bold; color: #3fb950; letter-spacing: 4px; }}
  .sig-valid {{ color: #3fb950; font-weight: bold; }}
  .sig-invalid {{ color: #f85149; font-weight: bold; }}
  .metric {{ display: inline-block; margin: 4px 8px; padding: 4px 12px; background: #21262d; border-radius: 12px; font-size: 13px; }}
  .metric .val {{ color: #58a6ff; font-weight: bold; }}
  .chart-container {{ text-align: center; margin: 12px 0; }}
  ul {{ margin-left: 20px; }}
  li {{ margin: 4px 0; }}
</style>
</head>
<body>
<div class="container">
  <div class="header">
    <h1>VQT Certificate Dashboard</h1>
    <p class="subtitle">Circuit: {circuit_name}</p>
  </div>

  <h2>Circuit Diagrams</h2>
  <div class="grid">
    <div class="card">
      <h3>Original Circuit</h3>
      <pre>{orig_ascii}</pre>
      <div>
        <span class="metric">Gates: <span class="val">{original_circuit.gate_count}</span></span>
        <span class="metric">Depth: <span class="val">{original_circuit.depth}</span></span>
      </div>
    </div>
    <div class="card">
      <h3>Optimized Circuit</h3>
      <pre>{opt_ascii}</pre>
      <div>
        <span class="metric">Gates: <span class="val">{optimized_circuit.gate_count}</span></span>
        <span class="metric">Depth: <span class="val">{optimized_circuit.depth}</span></span>
      </div>
    </div>
  </div>

  <h2>Optimization Summary</h2>
  <div class="card">
    <ul>
      {opt_steps_html}
    </ul>
  </div>

  <h2>Gate Count Comparison</h2>
  <div class="card chart-container">
    {bar_chart_svg}
  </div>

  <h2>Hash Chain</h2>
  <div class="card chart-container">
    {hash_chain_svg}
  </div>

  <h2>Equivalence Verification</h2>
  <div class="card" style="text-align:center;">
    <p style="margin-bottom:8px;">Fidelity: <strong>{fidelity_val:.8f}</strong></p>
    <span class="fidelity-badge {fidelity_class}">{fidelity_label}</span>
  </div>

  <div class="certified-stamp">
    <div class="label">CERTIFIED</div>
    <p style="margin-top:8px;">Certificate Hash: <code>{cert_hash}</code></p>
    <p>{sig_status}</p>
  </div>

  <h2>Certificate Details</h2>
  <div class="card">
    <p><strong>Circuit:</strong> {circuit_name}</p>
    <p><strong>Original Hash:</strong> <code>{orig_hash}</code></p>
    <p><strong>Optimized Hash:</strong> <code>{opt_hash}</code></p>
    <p><strong>Results Hash:</strong> <code>{results_hash}</code></p>
    <p><strong>Backend:</strong> {html.escape(certificate.backend_name)}</p>
    <p><strong>Version:</strong> {html.escape(certificate.toolkit_version)}</p>
  </div>
</div>
</body>
</html>
'''


def save_dashboard(html_content: str, filepath: str) -> None:
    """Write the HTML dashboard to a file."""
    with open(filepath, 'w', encoding='utf-8') as f:
        f.write(html_content)
