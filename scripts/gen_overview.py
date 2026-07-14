#!/usr/bin/env python3
"""Generate site/overview.html — the mathematical overview on the landing page:

  1. a precise statement of the Poincaré conjecture;
  2. the architecture of Perelman's proof, with each step linked to the
     matching blueprint chapter.

Math is LaTeX ($...$) rendered by the landing page's KaTeX. Edit the data below
and re-run `python3 scripts/gen_overview.py`.
"""
from __future__ import annotations

from pathlib import Path

OUT = Path(__file__).resolve().parent.parent / "site" / "overview.html"

CHEV = ('<svg class="chev" viewBox="0 0 24 24" width="20" height="20" aria-hidden="true">'
        '<path d="M6 9l6 6 6-6" fill="none" stroke="currentColor" stroke-width="2" '
        'stroke-linecap="round" stroke-linejoin="round"/></svg>')


def pc_term(label: str, definition: str, key: str) -> str:
    return (f'<span class="pc-term" tabindex="0" aria-describedby="pc-tip-{key}">'
            f'{label}<span class="pc-tip" id="pc-tip-{key}" role="tooltip">'
            f'{definition}</span></span>')


def statement_section() -> str:
    manifold = pc_term(
        r'topological $3$-manifold',
        r'A Hausdorff, second-countable space locally homeomorphic to $\mathbb{R}^3$.',
        'manifold')
    closed = pc_term(
        'closed',
        r'Compact and without boundary: $M$ is compact and $\partial M=\varnothing$.',
        'closed')
    connected = pc_term(
        'connected',
        r'$M$ has one connected component; for a manifold, this is equivalent to path-connectedness.',
        'connected')
    fundamental_group = pc_term(
        r'$\pi_1(M)=0$',
        r'For a basepoint $x\in M$, $\pi_1(M,x)$ is the group of based loops modulo homotopy. Triviality means every loop is null-homotopic.',
        'fundamental-group')
    conclusion = pc_term(
        r'$M\cong S^3$',
        r'Here $\cong$ denotes homeomorphism and $S^3=\{x\in\mathbb{R}^4:\lVert x\rVert=1\}$.',
        'conclusion')
    return ('<section class="pc-statement">'
            '<div class="pc-heading">'
            '<div class="pc-kicker">Geometric topology</div>'
            '<h2 id="pc-title">The Poincaré Conjecture</h2>'
            '<p>In dimension three, simple connectivity completely determines '
            'the topology of a closed manifold.</p></div>'
            '<div class="pc-theorem" aria-labelledby="pc-title">'
            '<div class="pc-theorem-label">Conjecture</div>'
            f'<p>Let $M$ be a {closed}, {connected} {manifold}. '
            f'If {fundamental_group}, then {conclusion}.</p></div>'
            '<p class="pc-bridge">Perelman proves this classification by evolving '
            'a Riemannian metric under Ricci flow, resolving singularities by '
            'surgery, and recovering the topology from finite-time extinction.</p>'
            '</section>')


# ── 2. the shape of the proof — clean flow, hover for detail ───────────────
P = "MorganTian/dashboard.html"
# (label, LaTeX detail summary, chapter href or None)
PHASES = [
    ("1", "#23479b", "Control the flow and its singularities", [
        ("Ricci flow", r"The metric evolves by $\partial_t g_{ij} = -2R_{ij}$; the maximum principle bounds curvature and Hamilton compactness takes limits of rescalings.", f"{P}#ch-4"),
        ("κ-noncollapsing", r"Perelman's reduced volume is monotone along the flow, forcing $\operatorname{Vol} B(x,r) \ge \kappa\, r^3$ where $|\mathrm{Rm}| \le r^{-2}$ — the flow never collapses.", f"{P}#ch-8"),
        ("κ-solutions", r"Blowing up at a singularity gives an ancient, $\kappa$-noncollapsed, nonnegatively-curved model.", f"{P}#ch-10"),
    ]),
    ("2", "#19734c", "Model the singularities, then cut them out", [
        ("Canonical neighborhoods", r"Every high-curvature point lies in a neck $\approx S^2 \times \mathbb{R}$ or a cap — a short, fixed list of local models.", f"{P}#ch-20"),
        ("Ricci flow with surgery", r"Cut along $\delta$-necks, glue in capped standard solutions, and restart; the parameters keep the flow $\kappa$-noncollapsed and canonical.", f"{P}#ch-16"),
        ("Long-time existence", r"Surgery times do not accumulate, so the flow with surgery runs for all $t \ge 0$.", f"{P}#ch-15"),
    ]),
    ("3", "#c2410c", r"Recover the topology under $\pi_1(M)=0$", [
        ("Finite-time extinction", r"A min-max width associated to nontrivial $\pi_2$ or $\pi_3$ decreases under the flow and forces extinction in finite time.", f"{P}#ch-19"),
        ("Surgery topology", r"Tracking neck surgeries and discarded components yields a connected-sum decomposition into spherical space forms and $S^2$-bundles over $S^1$.", f"{P}#ch-18"),
    ]),
]
GOAL = (r"$M \cong S^3$",
        r"Van Kampen turns connected sums into free products of fundamental groups. Trivial $\pi_1(M)$ excludes the nonspherical summands and nontrivial spherical space forms.")


def proof_section() -> str:
    out = ['<div class="proof-heading"><div class="pc-kicker">Formalization roadmap</div>'
           '<h3>The proof architecture</h3>'
           '<p>The formal development follows the analytic and topological '
           'dependencies in Perelman\'s argument.</p></div>', '<div class="pm">']
    for i, (n, color, title, items) in enumerate(PHASES):
        chips = []
        for label, detail, href in items:
            tag, attrs = ("a", f' href="{href}"') if href else ("span", ' tabindex="0"')
            chips.append(f'<{tag} class="pm-i"{attrs}>{label}<span class="pm-d">{detail}</span></{tag}>')
        out.append(f'<div class="pm-phase" style="--pc:{color}">'
                   f'<div class="pm-h"><span class="pm-n">{n}</span>{title}</div>'
                   f'<div class="pm-items">{"".join(chips)}</div></div>')
        out.append(f'<div class="pm-arrow">{CHEV}</div>')
    out.append(f'<div class="pm-goal"><div class="pm-goal-eq">{GOAL[0]}</div>'
               f'<div class="pm-goal-s">{GOAL[1]}</div></div>')
    out.append('</div>')
    return "\n".join(out)


def build() -> str:
    return "\n".join([statement_section(), proof_section(), _STYLE])


_STYLE = r"""<style>
/* theorem statement */
.overview{margin:44px -24px 0;padding:44px 24px 52px;background:var(--panel);
 border-top:1px solid var(--line);border-bottom:1px solid var(--line)}
.pc-statement{max-width:760px;margin:0 auto}
.pc-heading{text-align:center;max-width:650px;margin:0 auto}
.pc-kicker{text-transform:uppercase;letter-spacing:.09em;color:var(--accent);
 font-weight:800;font-size:11px;margin-bottom:8px}
.pc-heading h2,.proof-heading h3{letter-spacing:0;color:var(--fg)}
.pc-heading h2{font-size:clamp(27px,3vw,34px);line-height:1.18;margin:0 0 10px;font-weight:800}
.pc-heading p,.proof-heading p{margin:0;color:var(--muted);font-size:15px;line-height:1.6}
.pc-theorem{margin:28px 0 20px;padding:23px 26px 24px;background:var(--bg);
 border-left:4px solid var(--accent);border-radius:0 6px 6px 0}
.pc-theorem-label{text-transform:uppercase;letter-spacing:.08em;color:var(--muted);
 font-size:10.5px;font-weight:800;margin-bottom:8px}
.pc-theorem p{margin:0;font:500 clamp(18px,2.2vw,22px)/1.65 Georgia,"Times New Roman",serif;text-align:left}
.pc-theorem .katex{font-size:1.06em}
.pc-bridge{max-width:66ch;margin:0 auto;color:var(--fg);font-size:14px;line-height:1.7}
.pc-term{position:relative;display:inline-block;cursor:help;border-bottom:1px dotted var(--accent);outline:none}
.pc-term:focus-visible{border-radius:2px;outline:2px solid color-mix(in srgb,var(--accent) 35%,transparent);outline-offset:3px}
.pc-tip{position:absolute;left:50%;top:calc(100% + 10px);transform:translateX(-50%);
 width:max-content;max-width:330px;padding:10px 13px;background:var(--panel);color:var(--fg);
 border:1px solid var(--line);border-radius:6px;box-shadow:0 10px 30px rgba(20,25,35,.18);
 font:400 12.5px/1.55 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Helvetica,sans-serif;
 text-align:left;white-space:normal;opacity:0;visibility:hidden;transition:opacity .13s;z-index:60;pointer-events:none}
.pc-term:hover>.pc-tip,.pc-term:focus>.pc-tip{opacity:1;visibility:visible}
/* proof details */
.pm-d{position:absolute;left:50%;top:calc(100% + 10px);transform:translateX(-50%);
 width:max-content;max-width:290px;white-space:normal;text-align:left;background:var(--panel);color:var(--fg);
 border:1px solid var(--line);font-size:12.5px;font-weight:400;line-height:1.5;padding:10px 13px;border-radius:6px;
 box-shadow:0 10px 34px rgba(20,25,35,.2);opacity:0;visibility:hidden;transition:opacity .13s;z-index:50;pointer-events:none}
/* the shape of the proof */
.proof-heading{text-align:center;max-width:650px;margin:50px auto 20px}
.proof-heading h3{font-size:24px;line-height:1.25;margin:0 0 8px;font-weight:800}
.pm{max-width:680px;margin:0 auto}
.pm-phase{background:var(--bg);border:1px solid var(--line);border-left:4px solid var(--pc);
 border-radius:6px;padding:15px 18px}
.pm-h{display:flex;align-items:center;gap:11px;font-weight:700;font-size:15.5px;letter-spacing:0;margin-bottom:12px}
.pm-n{flex:none;width:25px;height:25px;border-radius:50%;background:var(--pc);color:#fff;font-size:13.5px;font-weight:800;
 display:flex;align-items:center;justify-content:center}
.pm-items{display:flex;flex-wrap:wrap;gap:9px}
.pm-i{position:relative;display:inline-flex;align-items:center;gap:6px;font-size:13px;color:var(--fg);
 background:var(--soft);border:1px solid var(--line);border-radius:999px;padding:5px 13px;cursor:pointer;
 text-decoration:none;transition:.13s}
.pm-i:hover{border-color:var(--pc);background:#fff}
a.pm-i::after{content:"→";color:var(--pc);font-weight:700;font-size:12px;opacity:.6}
.pm-i:hover .pm-d,.pm-i:focus .pm-d{opacity:1;visibility:visible}
.pm-arrow{display:flex;justify-content:center;color:var(--empty);margin:5px 0}
.pm-goal{text-align:center;background:#272b33;color:#fff;border-radius:6px;padding:20px}
.pm-goal-eq{font-size:24px}.pm-goal-eq .katex{color:#fff}
.pm-goal-s{font-size:12.5px;opacity:.92;margin-top:5px;max-width:52ch;margin-left:auto;margin-right:auto}
.pm-goal-s .katex{color:#fff}
@media(max-width:640px){
 .overview{margin-top:34px;padding-top:36px;padding-bottom:42px}
 .pc-theorem{padding:19px 18px 20px}
 .pc-theorem p{font-size:18px;line-height:1.7}
 .pc-tip{position:fixed;left:16px;right:16px;top:auto;bottom:16px;transform:none;width:auto;max-width:none}
 .pm-items{display:grid;grid-template-columns:1fr}
 .pm-i{justify-content:space-between}
 .pm-d{left:0;right:0;transform:none;width:auto;max-width:none}
}
</style>"""


if __name__ == "__main__":
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(build(), encoding="utf-8")
    print(f"wrote {OUT} ({len(OUT.read_text())//1024} KB)")
