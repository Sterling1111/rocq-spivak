#!/bin/bash
# Navigate to the root directory of the Coq project
cd "$(dirname "$0")/../../.." || exit

FOLDER="Calculus/Chapter11/Problem3"
COQ_FILE="Calculus/Chapter11/Problem3.v"
VO_FILE="Calculus/Chapter11/Problem3.vo"

echo "Generating PNG plots for chapter 11 problem 3..."

if ! command -v gnuplot >/dev/null 2>&1; then
    echo "gnuplot not found; skipping plot generation for chapter 11 problem 3." >&2
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

# Define a function to generate a plot
generate_plot() {
    local base_name="$1"
    local func_expr="$2"
    local func_label="$3"
    shift 3
    local files=("$@")
    
    local temp_main="${FOLDER}/temp_main_${base_name}.gp"
    echo "set terminal pngcairo size 800,600 enhance font 'arial,12'" > "$temp_main"
    echo "set output '${FOLDER}/${base_name}.png'" >> "$temp_main"
    echo "set size ratio -1" >> "$temp_main"
    echo "set xrange [-5:5]" >> "$temp_main"
    echo "set yrange [-5:5]" >> "$temp_main"
    echo "set title '${func_label}'" >> "$temp_main"
    
    echo "set samples 2000" >> "$temp_main"
    # Plot only the native smooth curve without line label, breaking lines at asymptotes
    echo "plot (abs(${func_expr}) > 50 ? NaN : (${func_expr})) notitle with lines linewidth 2 lc rgb 'purple'" >> "$temp_main"
    
    gp_log="$(mktemp)"
    if ! gnuplot "$temp_main" >"$gp_log" 2>&1; then
        cat "$gp_log" >&2
        rm -f "$gp_log" "$temp_main"
        exit 1
    fi
    rm -f "$gp_log" "$temp_main"
}

# Generate plots
f_i_files=("$FOLDER"/f_i_*.gp)
generate_plot "f_i" "x + 1/x" "x + 1/x" "${f_i_files[@]}"

f_ii_files=("$FOLDER"/f_ii_*.gp)
generate_plot "f_ii" "x + 3/x**2" "x + 3/x^2" "${f_ii_files[@]}"

f_iii_files=("$FOLDER"/f_iii_*.gp)
generate_plot "f_iii" "x**2 / (x**2 - 1)" "x^2 / (x^2 - 1)" "${f_iii_files[@]}"

f_iv_files=("$FOLDER"/f_iv.gp)
generate_plot "f_iv" "1 / (1 + x**2)" "1 / (1 + x^2)" "${f_iv_files[@]}"

# Cleanup original .gp files
rm -f "$FOLDER"/*.gp
