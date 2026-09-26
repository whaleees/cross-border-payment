"""Turn a finished benchmark run into results/: CSVs, two charts and README.md.

    cargo bench                  # first: both bench targets (pin the clock - guide-benchmark/07)
    python scripts/report.py     # then: runs the size + FAR/FRR tests, reads criterion, writes results/

Criterion's numbers are read from $CARGO_TARGET_DIR/criterion (or ./target/criterion).
"""

import argparse
import csv
import datetime
import json
import os
import pathlib
import re
import subprocess
import sys

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
from matplotlib.ticker import FixedFormatter, FixedLocator, FuncFormatter, NullFormatter  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
CRITERION = pathlib.Path(os.environ.get("CARGO_TARGET_DIR", ROOT / "target")) / "criterion"

# (name in the thesis, bench id stem, key in the proof-size line)
PROTOCOLS = [
    ("Π.IDEq", "ideq", "ideq"),
    ("Π.VVer", "vver", "vver"),
    ("Π.VEq", "veq", "veq"),
    ("Π.FullEq", "fulleq", "fulleq"),
    ("Π.TxVer", "txver", "txver"),
    ("Π.MIDEq, n = 10", "mideq_n10", "mideq"),
]
NS = [2, 5, 10, 50, 100, 500, 1000]
MS = [1, 10, 100, 1000, 10000]

data_times = []  # modification times of every estimates.json read


# ---- reading the measurements --------------------------------------------------------

def estimate(*path):
    """(mean, standard deviation) in microseconds, from criterion's estimates.json."""
    f = CRITERION.joinpath(*map(str, path), "new", "estimates.json")
    e = json.loads(f.read_text())
    data_times.append(f.stat().st_mtime)
    return e["mean"]["point_estimate"] / 1e3, e["std_dev"]["point_estimate"] / 1e3


def cargo(*args):
    """Run cargo; retry Windows Defender's transient 'Access is denied' (os error 5)."""
    for _ in range(3):
        r = subprocess.run(["cargo", *args], cwd=ROOT, capture_output=True, text=True,
                           encoding="utf-8", errors="replace")
        out = r.stdout + r.stderr
        if "os error 5" not in out:
            break
    if r.returncode != 0:
        sys.exit(f"cargo {' '.join(args)} failed:\n{out[-3000:]}")
    return out


def proof_sizes():
    """The line printed by tests/sizes.rs, and its numbers: {'commitment': 32, 'ideq': 96, ...}."""
    out = cargo("test", "proof_sizes", "--", "--nocapture")
    line = next(l for l in out.splitlines() if l.startswith("commitment "))
    words = line.split()
    return line, dict(zip(words[::2], map(int, words[1::2])))


def rates():
    """The FAR/FRR table printed by tests/rates.rs (release build), and its rows."""
    out = cargo("test", "--release", "--test", "rates", "--", "--ignored", "--nocapture")
    lines = out.splitlines()
    start = next(i for i, l in enumerate(lines) if l.startswith("FAR / FRR over"))
    end = next(i for i, l in enumerate(lines) if "errors in" in l)
    table = lines[start:end + 1]
    rows = []
    for l in table:
        m = re.match(r"^(.+?)\s{2,}(.+?)\s+(\d+) / (\d+)\s+(\d+) (false rejections|false approvals)$", l)
        if m:
            rows.append({"protocol": m[1].strip(), "scenario": m[2].strip(), "accepted": int(m[3]),
                         "runs": int(m[4]), "errors": int(m[5]), "honest": m[6] == "false rejections"})
    return "\n".join(table), rows


def sh(*cmd):
    try:
        return subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True,
                              encoding="utf-8", errors="replace").stdout.strip()
    except OSError:
        return ""


def machine():
    """What the numbers were measured on. Windows queries; blanks elsewhere."""
    def ps(query):
        return sh("powershell", "-NoProfile", "-Command", query)

    plan = re.search(r"\((.+)\)", sh("powercfg", "/getactivescheme"))
    maxstate = re.search(r"Current AC Power Setting Index: 0x([0-9a-fA-F]+)",
                         sh("powercfg", "/query", "SCHEME_CURRENT", "SUB_PROCESSOR", "PROCTHROTTLEMAX"))
    battery = ps("(Get-CimInstance Win32_Battery | Select-Object -First 1).BatteryStatus")
    lock = (ROOT / "Cargo.lock").read_text()
    criterion = re.search(r'name = "criterion"\nversion = "([^"]+)"', lock)
    dirty = sh("git", "status", "--porcelain", "--", ".", ":!results")
    return {
        "Date": datetime.datetime.now().strftime("%Y-%m-%d %H:%M"),
        "Git commit": sh("git", "rev-parse", "--short", "HEAD") + (" (+ uncommitted changes)" if dirty else ""),
        "CPU": ps("(Get-CimInstance Win32_Processor | Select-Object -First 1).Name"),
        "Cores / threads": ps("$p = Get-CimInstance Win32_Processor | Select-Object -First 1; "
                              "\"$($p.NumberOfCores) / $($p.NumberOfLogicalProcessors)\""),
        "RAM": ps("'{0:N0} GB' -f ((Get-CimInstance Win32_ComputerSystem).TotalPhysicalMemory / 1GB)"),
        "OS": ps("$o = Get-CimInstance Win32_OperatingSystem; \"$($o.Caption) (build $($o.BuildNumber))\""),
        "Power": {"2": "on AC"}.get(battery, f"on battery (status {battery})" if battery else "unknown"),
        "Power plan": plan[1] if plan else "unknown",
        "Maximum processor state (AC)": f"{int(maxstate[1], 16)} %" if maxstate else "unknown",
        "rustc": sh("rustc", "-V"),
        "criterion": criterion[1] if criterion else "unknown",
    }


# ---- charts: black and white, SVG + 300-dpi PNG ----------------------------------------

INK, GRID = "black", "#d0d0d0"
plt.rcParams.update({
    "font.family": "sans-serif", "font.size": 9,
    "axes.edgecolor": INK, "axes.labelcolor": INK, "axes.linewidth": 0.8,
    "axes.spines.top": False, "axes.spines.right": False,
    "xtick.color": INK, "ytick.color": INK,
    "svg.fonttype": "none", "svg.hashsalt": "ibc",
})
# The Advanced method: solid line, filled circle (white ring). The Basic baseline:
# dashed line, hollow square. Line style + marker carry identity, never colour.
ADVANCED = dict(color=INK, linestyle="-", linewidth=1.5, marker="o", markersize=6,
                markerfacecolor=INK, markeredgecolor="white", markeredgewidth=1.2, zorder=3)
BASELINE = dict(color=INK, linestyle=(0, (5, 3)), linewidth=1.5, marker="s", markersize=5.5,
                markerfacecolor="white", markeredgecolor=INK, markeredgewidth=1.2, zorder=3)


def grid(ax):
    ax.grid(True, which="major", color=GRID, linewidth=0.5, linestyle="-")
    ax.set_axisbelow(True)


def log_x(ax, labelled, unlabelled, right):
    """Log x-axis: labels only where they cannot collide; other measured points get a bare tick."""
    ax.set_xscale("log")
    ax.xaxis.set_major_locator(FixedLocator(labelled))
    ax.xaxis.set_major_formatter(FixedFormatter([f"{t:,}" for t in labelled]))
    ax.xaxis.set_minor_locator(FixedLocator(unlabelled))
    ax.xaxis.set_minor_formatter(NullFormatter())
    ax.set_xlim(min(labelled) / 1.4, right)


def end_label(ax, x, y, text):
    ax.annotate(text, (x, y), xytext=(6, 0), textcoords="offset points", va="center", fontsize=8)


def save(fig, stem):
    fig.savefig(stem.with_suffix(".svg"), metadata={"Date": None})
    fig.savefig(stem.with_suffix(".png"), dpi=300)
    plt.close(fig)


def fmt_ms(us):
    ms = us / 1e3
    return f"{ms:.3g} ms" if ms < 100 else f"{ms:,.0f} ms"


def chart_mideq(rows, stem):
    fig, axes = plt.subplots(1, 2, figsize=(6.6, 3.0), sharey=True)
    for ax, key, title in [(axes[0], "prove", "(a) Proving"), (axes[1], "verify", "(b) Verifying")]:
        base = [r[f"basic_{key}"] / 1e3 for r in rows]
        adv = [r[f"mideq_{key}"] / 1e3 for r in rows]
        ax.plot(NS, base, label="n − 1 separate Π.IDEq proofs", **BASELINE)
        ax.plot(NS, adv, label="one Π.MIDEq proof", **ADVANCED)
        log_x(ax, [2, 10, 100, 1000], [5, 50, 500], 4000)
        ax.set_yscale("log")
        ax.yaxis.set_major_formatter(FuncFormatter(lambda v, _: f"{v:g}"))
        grid(ax)
        ax.set_title(title, loc="left", fontsize=9, fontweight="bold")
        ax.set_xlabel("n (commitments sharing one identity)")
        end_label(ax, NS[-1], base[-1], fmt_ms(base[-1] * 1e3))
        end_label(ax, NS[-1], adv[-1], fmt_ms(adv[-1] * 1e3))
    axes[0].set_ylabel("time (ms, log scale)")
    handles, labels = axes[0].get_legend_handles_labels()
    # Long legend keys, so the dash pattern -- the only thing telling the series apart -- shows.
    fig.legend(handles, labels, loc="upper center", ncol=2, frameon=False, bbox_to_anchor=(0.5, 1.0),
               handlelength=4)
    fig.tight_layout(rect=(0, 0, 1, 0.91))
    save(fig, stem)


def chart_batch(rows, stem):
    fig, ax = plt.subplots(figsize=(5.2, 3.0))
    indiv = [r["individual_per_proof"] for r in rows]
    batch = [r["batch_per_proof"] for r in rows]
    ax.plot(MS, indiv, label="m separate Π.IDEq verifications", **BASELINE)
    ax.plot(MS, batch, label="one BatchVer call", **ADVANCED)
    log_x(ax, MS, [], 40000)
    ax.set_ylim(0, max(indiv + batch) * 1.15)
    grid(ax)
    ax.set_xlabel("m (proofs verified)")
    ax.set_ylabel("verification time per proof (µs)")
    end_label(ax, MS[-1], indiv[-1], f"{indiv[-1]:.0f} µs")
    end_label(ax, MS[-1], batch[-1], f"{batch[-1]:.0f} µs")
    ax.legend(loc="upper center", ncol=2, frameon=False, bbox_to_anchor=(0.5, 1.16), handlelength=4)
    fig.tight_layout()
    save(fig, stem)


# ---- the report ----------------------------------------------------------------------------

def write_csv(path, header, rows):
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(header)
        w.writerows(rows)


def crossing(xs, ys, limit):
    """The x at which ys first passes limit, by linear interpolation (None if it never does)."""
    for (x0, y0), (x1, y1) in zip(zip(xs, ys), zip(xs[1:], ys[1:])):
        if y0 <= limit < y1:
            return x0 + (limit - y0) * (x1 - x0) / (y1 - y0)
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--out", default=str(ROOT / "results"), help="output folder (default: results/)")
    out = pathlib.Path(parser.parse_args().out)
    out.mkdir(parents=True, exist_ok=True)
    sys.stdout.reconfigure(encoding="utf-8")

    print("reading criterion estimates from", CRITERION)
    commit = estimate("protocols", "commit")
    prove = {stem: estimate("protocols", f"{stem}_prove") for _, stem, _ in PROTOCOLS}
    verify = {stem: estimate("protocols", f"{stem}_verify") for _, stem, _ in PROTOCOLS}
    pair_prove, pair_verify = estimate("protocols", "basic_tx_prove"), estimate("protocols", "basic_tx_verify")
    e2e = estimate("tps", "transaction")
    scaling = []
    for n in NS:
        row = {"n": n}
        for f in ["mideq_prove", "basic_prove", "mideq_verify", "basic_verify"]:
            row[f], row[f + "_sd"] = estimate("mideq_vs_ideq", f, n)
        scaling.append(row)
    batching = []
    for m in MS:
        (bt, bsd), (it, isd) = estimate("batchver_vs_individual", "batch", m), estimate("batchver_vs_individual", "individual", m)
        batching.append({"m": m, "batch": bt, "batch_sd": bsd, "individual": it, "individual_sd": isd,
                         "batch_per_proof": bt / m, "individual_per_proof": it / m})

    print("running the proof-size test")
    size_line, size = proof_sizes()
    print("running the FAR/FRR test (release; minutes)")
    rates_table, rate_rows = rates()
    print("collecting machine details")
    info = machine()
    first, last = (datetime.datetime.fromtimestamp(t).strftime("%Y-%m-%d %H:%M") for t in (min(data_times), max(data_times)))
    info["Criterion data written"] = first if first == last else f"{first} to {last}"

    # CSV twins (the table view of every chart)
    write_csv(out / "protocols.csv", ["benchmark", "mean_us", "std_dev_us"],
              [["protocols/commit", f"{commit[0]:.2f}", f"{commit[1]:.2f}"]]
              + [[f"protocols/{s}_{k}", f"{v[s][0]:.2f}", f"{v[s][1]:.2f}"]
                 for _, s, _ in PROTOCOLS for k, v in (("prove", prove), ("verify", verify))]
              + [["protocols/basic_tx_prove", f"{pair_prove[0]:.2f}", f"{pair_prove[1]:.2f}"],
                 ["protocols/basic_tx_verify", f"{pair_verify[0]:.2f}", f"{pair_verify[1]:.2f}"],
                 ["tps/transaction", f"{e2e[0]:.2f}", f"{e2e[1]:.2f}"]])
    write_csv(out / "mideq_vs_ideq.csv",
              ["n", "mideq_prove_us", "mideq_prove_sd_us", "basic_prove_us", "basic_prove_sd_us",
               "mideq_verify_us", "mideq_verify_sd_us", "basic_verify_us", "basic_verify_sd_us"],
              [[r["n"]] + [f"{r[k]:.1f}" for k in ["mideq_prove", "mideq_prove_sd", "basic_prove", "basic_prove_sd",
                                                    "mideq_verify", "mideq_verify_sd", "basic_verify", "basic_verify_sd"]]
               for r in scaling])
    write_csv(out / "batchver_vs_individual.csv",
              ["m", "batch_total_us", "batch_sd_us", "batch_per_proof_us",
               "individual_total_us", "individual_sd_us", "individual_per_proof_us", "individual_over_batch"],
              [[r["m"], f"{r['batch']:.1f}", f"{r['batch_sd']:.1f}", f"{r['batch_per_proof']:.2f}",
                f"{r['individual']:.1f}", f"{r['individual_sd']:.1f}", f"{r['individual_per_proof']:.2f}",
                f"{r['individual'] / r['batch']:.2f}"] for r in batching])
    (out / "sizes.txt").write_text(size_line + "\n", encoding="utf-8")
    (out / "rates.txt").write_text(rates_table + "\n", encoding="utf-8")

    chart_mideq(scaling, out / "chart1_mideq_vs_ideq")
    chart_batch(batching, out / "chart2_batchver_vs_individual")

    # README.md -- every number below is computed from the files above
    names = {stem: name for name, stem, _ in PROTOCOLS}
    slow_p = max(prove, key=lambda s: prove[s][0])
    slow_v = max(verify, key=lambda s: verify[s][0])
    tps_adv, tps_basic, tps_e2e = 1e6 / verify["txver"][0], 1e6 / pair_verify[0], 1e6 / e2e[0]
    honest = [r for r in rate_rows if r["honest"]]
    adversarial = [r for r in rate_rows if not r["honest"]]
    false_rej = sum(r["runs"] - r["accepted"] for r in honest)
    false_app = sum(r["accepted"] for r in adversarial)
    runs = rate_rows[0]["runs"]
    proof_bytes = [size[key] for _, _, key in PROTOCOLS]
    ok = lambda b: "✓" if b else "✗"

    def us(v):
        return f"{v[0]:,.0f} ± {v[1]:,.0f}"

    big, small = scaling[-1], scaling[0]
    cross_v = crossing(NS, [r["mideq_verify"] for r in scaling], 5000)
    cross_bv = crossing(NS, [r["basic_verify"] for r in scaling], 5000)
    b_last, b_first = batching[-1], batching[0]
    boost_on = info["Maximum processor state (AC)"] == "100 %"

    md = [
        "# Benchmark results",
        "",
        "Generated by `scripts/report.py` from one `cargo bench` run plus the size and FAR/FRR tests. "
        "Every number below comes from the files in this folder. How to read them: "
        "`guide-benchmark/01-targets.md` (expected shapes) and `guide-benchmark/07-reporting.md`.",
        "",
    ]
    if boost_on:
        md += ["> **Warning:** CPU boost was on (maximum processor state 100 %). Timings can drift between "
               "benchmarks; pin the clock and re-run before quoting ratios (guide-benchmark/07).", ""]
    md += ["## Run", "", "| | |", "|---|---|"] + [f"| {k} | {v} |" for k, v in info.items()] + [""]
    md += [
        "## Metric targets (proposal Table 3.1; commit time from the RTM)",
        "",
        "| Metric | Target | Measured | Pass |",
        "|---|---|---|---|",
        f"| Commitment generation time | < 10 ms | {fmt_ms(commit[0])} | {ok(commit[0] < 10_000)} |",
        f"| Proof generation time (slowest) | < 10 ms | {fmt_ms(prove[slow_p][0])} ({names[slow_p]}) | {ok(prove[slow_p][0] < 10_000)} |",
        f"| Verification time (slowest) | < 5 ms | {fmt_ms(verify[slow_v][0])} ({names[slow_v]}) | {ok(verify[slow_v][0] < 5_000)} |",
        f"| Throughput (transactions verified per second, one core) | > 100 TPS | {tps_adv:,.0f} (Π.TxVer), "
        f"{tps_basic:,.0f} (Π.IDEq + Π.VVer); end to end {tps_e2e:,.0f} | {ok(min(tps_adv, tps_basic) > 100)} |",
        f"| Commitment size | 32–64 B | {size['commitment']} B | {ok(32 <= size['commitment'] <= 64)} |",
        f"| Communication complexity | O(log p) | proofs are {min(proof_bytes)}–{max(proof_bytes)} B: a fixed number "
        f"of 32-byte elements | {ok(all(b % 32 == 0 for b in proof_bytes))} |",
        "| Soundness error | ≤ 1/p | analytical: Theorems 1–6 (a factor Q in the random-oracle model) | — |",
        f"| False approval rate | 0 | {false_app} / {runs * len(adversarial):,} adversarial runs | {ok(false_app == 0)} |",
        f"| False rejection rate | 0 | {false_rej} / {runs * len(honest):,} honest runs | {ok(false_rej == 0)} |",
        "",
        "## Per protocol (task a) — mean ± standard deviation, µs",
        "",
        "| Protocol | Prove | Verify | Proof size |",
        "|---|---|---|---|",
    ]
    md += [f"| {name} | {us(prove[s])} | {us(verify[s])} | {size[key]} B |" for name, s, key in PROTOCOLS]
    md += [
        f"| Commit | {us(commit)} | | {size['commitment']} B (commitment) |",
        "",
        "Mean ± standard deviation of criterion's samples (`new/estimates.json`), as Bab 3 asks. The line "
        "criterion prints in the terminal shows a different estimator (a regression slope), so its middle "
        "number can differ — most where the machine was noisy, which a large ± also shows.",
        "",
        "## Π.TxVer vs two separate proofs (task d) — µs",
        "",
        "| | Π.IDEq + Π.VVer | Π.TxVer | pair ÷ Π.TxVer |",
        "|---|---|---|---|",
        f"| Prove | {us(pair_prove)} | {us(prove['txver'])} | {pair_prove[0] / prove['txver'][0]:.2f}× |",
        f"| Verify | {us(pair_verify)} | {us(verify['txver'])} | {pair_verify[0] / verify['txver'][0]:.2f}× |",
        "",
        "## Chart 1 — Π.MIDEq vs n − 1 Π.IDEq (task b)",
        "",
        "![Chart 1](chart1_mideq_vs_ideq.png)",
        "",
        f"At n = {big['n']:,}: proving {fmt_ms(big['mideq_prove'])} vs {fmt_ms(big['basic_prove'])} "
        f"({big['basic_prove'] / big['mideq_prove']:.1f}× less), verifying {fmt_ms(big['mideq_verify'])} vs "
        f"{fmt_ms(big['basic_verify'])} ({big['basic_verify'] / big['mideq_verify']:.1f}× less). "
        f"At n = {small['n']}, Π.MIDEq is {small['mideq_verify'] / small['basic_verify']:.2f}× the time of the "
        f"single Π.IDEq to verify. Proof size: {size['mideq']} B for every n, against 96(n − 1) B.",
        "",
        f"Verification passes 5 ms at n ≈ {cross_v:.0f} for Π.MIDEq and at n ≈ {cross_bv:.0f} for the separate "
        "proofs (linear interpolation between measured points)."
        if cross_v and cross_bv else "",
        "",
        "Numbers: [mideq_vs_ideq.csv](mideq_vs_ideq.csv) · chart: [SVG](chart1_mideq_vs_ideq.svg), "
        "[PNG](chart1_mideq_vs_ideq.png)",
        "",
        "## Chart 2 — BatchVer vs individual verification (task c)",
        "",
        "![Chart 2](chart2_batchver_vs_individual.png)",
        "",
        f"Per proof at m = {b_last['m']:,}: {b_last['batch_per_proof']:.0f} µs in one batch vs "
        f"{b_last['individual_per_proof']:.0f} µs verified one by one "
        f"({b_last['individual'] / b_last['batch']:.2f}× faster). At m = {b_first['m']} the batch takes "
        f"{b_first['batch']:.0f} µs vs {b_first['individual']:.0f} µs.",
        "",
        "Numbers: [batchver_vs_individual.csv](batchver_vs_individual.csv) · chart: "
        "[SVG](chart2_batchver_vs_individual.svg), [PNG](chart2_batchver_vs_individual.png)",
        "",
        "## Proof sizes (task a)",
        "",
        "```",
        size_line,
        "```",
        "",
        "## False approval / rejection rates",
        "",
        "```",
        rates_table,
        "```",
        "",
    ]
    (out / "README.md").write_text("\n".join(md), encoding="utf-8")
    print("wrote", out)


if __name__ == "__main__":
    main()
