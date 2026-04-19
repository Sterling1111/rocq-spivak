#!/bin/bash
# Navigate to the root directory of the Coq project
cd "$(dirname "$0")/../../.." || exit

FOLDER="Calculus/Chapter18/Problem18"
COQ_FILE="Calculus/Chapter18/Problem18.v"
VO_FILE="Calculus/Chapter18/Problem18.vo"

echo "Generating PNG plots for chapter 18 problem 18..."

if ! command -v gnuplot >/dev/null 2>&1; then
    echo "gnuplot not found; skipping plot generation for chapter 18 problem 18." >&2
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
        f) func="f(x) = (1 + 1/x)^{x}" ; func_label="(1 + 1/x)^{x}" ;;
        *)  func="$base(x)" ; func_label="$base(x)" ;;
    esac
    
    temp_gp="temp_${base}.txt"
    echo "set terminal pngcairo size 800,800 enhance font 'arial,12'" > "$temp_gp"
    echo "set output '${FOLDER}/${base}.png'" >> "$temp_gp"
    echo "set title '${func}'" >> "$temp_gp"
    echo "set size ratio 1.25" >> "$temp_gp"
    
    # Overwrite 'notitle' to bring back the legend box
    # To make line thicknesses match perfectly in the legend and plot, we swap the generated 'filledcurves' for 'lines linewidth 2'
    sed "s|notitle with filledcurves|title '${func_label}' with lines linewidth 2|" "$f" | grep -v "pause mouse" >> "$temp_gp"
    
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
