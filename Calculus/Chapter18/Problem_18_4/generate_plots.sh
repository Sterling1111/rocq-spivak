#!/bin/bash
# Navigate to the root directory of the Coq project
cd "$(dirname "$0")/../../.." || exit

FOLDER="Calculus/Chapter18/Problem_18_4"
COQ_FILE="Calculus/Chapter18/Problem_18_4.v"
VO_FILE="Calculus/Chapter18/Problem_18_4.vo"

echo "Generaatng PNG plots forproblem 18_4..."

if ! command -v gnuplot >/dev/null 2>&1; then
    echo "gnuplot not found; skipping plot generation for problem 18_4." >&2
    exit 0
fi

mkdir -p "$FOLDER"
# Avoid deleting the script itself
find "$FOLDER" -type f ! -name 'generate_plots.sh' -delete

# Force re-compilation to generate .gp plots
rm -f "$VO_FILE"
coq_log="$(mktemp)"
if ! coqc -w "-deprecated-dirpath-Coq,-deprecated-since-9.0" -R Lib Lib -R Calculus Calculus -R ATTAM ATTAM -I src "$COQ_FILE" >"$coq_log" 2>&1; then
    cat "$coq_log" >&2
    rm -f "$coq_log"
    exit 1
fi
rm -f "$coq_log"

# Generate PNG plots from any existing .gp files
shopt -s nullglob
for f in "$FOLDER"/*.gp; do
    base=$(basename "$f" .gp)
    
    # Map the filename to its function equation for the title
    case $base in
        fa) func="fa(x) = e^{x + 1}" ; func_label="e^{x + 1}" ;;
        fb) func="fb(x) = e^{sin x}" ; func_label="e^{sin x}" ;;
        fc) func="fc(x) = e^{x} + e^{-x}" ; func_label="e^{x} + e^{-x}" ;;
        fd) func="fd(x) = e^{x} - e^{-x}" ; func_label="e^{x} - e^{-x}" ;;
        fe) func="fe(x) = (e^{x} - e^{-x}) / (e^{x} + e^{-x})" ; func_label="(e^{x} - e^{-x}) / (e^{x} + e^{-x})" ;;
        fc_prime) func="fc_prime(x) = e^{x} - e^{-x}" ; func_label="e^{x} - e^{-x}" ;;
        fd_prime) func="fd_prime(x) = e^{x} + e^{-x}" ; func_label="e^{x} + e^{-x}" ;;
        *)  func="$base(x)" ; func_label="$base(x)" ;;
    esac
    
    temp_gp="temp_${base}.txt"
    echo "set terminal pngcairo size 800,600 enhance font 'arial,12'" > "$temp_gp"
    echo "set output '${FOLDER}/${base}.png'" >> "$temp_gp"
    echo "set title '${func}'" >> "$temp_gp"
    echo "set size ratio -1" >> "$temp_gp"
    
    if [ "$base" = "fe" ]; then
        echo "set key top left" >> "$temp_gp"
    fi
    
    # Check if we need to plot exp(x) and exp(-x) with it
    extra_plots=""
    if [ "$base" = "fc" ] || [ "$base" = "fd" ]; then
        extra_plots=", exp(x) title 'e^{x}' with lines linewidth 2 linecolor rgb 'forest-green', exp(-x) title 'e^{-x}' with lines linewidth 2 linecolor rgb 'blue'"
    fi
    
    # Overwrite 'notitle' to bring back the legend box, and fold in extra formulas natively
    # To make line thicknesses match perfectly in the legend and plot, we swap the generated 'filledcurves' for 'lines linewidth 2'
    sed "s|notitle with filledcurves|title '${func_label}' with lines linewidth 2${extra_plots}|" "$f" | grep -v "pause mouse" >> "$temp_gp"
    
    gp_log="$(mktemp)"
    if ! gnuplot "$temp_gp" >"$gp_log" 2>&1; then
        cat "$gp_log" >&2
        rm -f "$gp_log" "$temp_gp"
        exit 1
    fi
    rm -f "$gp_log"
    rm -f "$temp_gp"
done

# Cleanup .gp files
rm -f "$FOLDER"/*.gp
