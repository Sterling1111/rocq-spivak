#!/bin/bash
# Navigate to the root directory of the Coq project
cd "$(dirname "$0")/../../.." || exit

FOLDER="Calculus/Chapter13/Problem8"
COQ_FILE="Calculus/Chapter13/Problem8.v"
VO_FILE="Calculus/Chapter13/Problem8.vo"

echo "Generating PNG plots for chapter 13 problem 8..."

if ! command -v gnuplot >/dev/null 2>&1; then
    echo "gnuplot not found; skipping plot generation for chapter 13 problem 8." >&2
    exit 0
fi

mkdir -p "$FOLDER"
find "$FOLDER" -type f ! -name 'generate_plots.sh' -delete

rm -f "$VO_FILE"
coq_log="$(mktemp)"
if ! coqc -w "-deprecated-dirpath-Coq,-deprecated-since-9.0" -R Lib Lib -R Calculus Calculus -R ATTAM ATTAM -I src "$COQ_FILE" >"$coq_log" 2>&1; then
    cat "$coq_log" >&2
    rm -f "$coq_log"
    exit 1
fi
rm -f "$coq_log"

extract_data() {
    local prefix="$1"
    grep -E '^(ox|dx|oy|dy) =' "$FOLDER/${prefix}.gp" | sed "s/^/${prefix}_/" >> temp.gp
    sed '1,/plot/d' "$FOLDER/${prefix}.gp" | sed '/^e$/,$d' > "${FOLDER}/${prefix}_data.txt"
}

# --- Graph (i) ---
echo "set terminal pngcairo size 800,600 enhance font 'arial,12'" > temp.gp
echo "set output '${FOLDER}/plot_i.png'" >> temp.gp
echo "set title 'Problem 8 (i)'" >> temp.gp
echo "set style fill transparent solid 0.3 noborder" >> temp.gp
echo "set samples 500" >> temp.gp
echo "set size ratio -1" >> temp.gp
extract_data fi
extract_data gi
cat << 'EOF' >> temp.gp
f(x) = x**2 / 2.0 + 2.0
g(x) = x**2
set xrange [-3:3]
plot '+' using 1:( ($1 >= -2 && $1 <= 2) ? f($1) : 1/0 ):(g($1)) with filledcurves title 'Area', \
     'Calculus/Chapter13/Problem8/fi_data.txt' using (fi_ox+fi_dx*$1):(fi_oy+fi_dy*$2) with lines linewidth 2 title 'f(x) = x^2/2 + 2', \
     'Calculus/Chapter13/Problem8/gi_data.txt' using (gi_ox+gi_dx*$1):(gi_oy+gi_dy*$2) with lines linewidth 2 title 'g(x) = x^2'
EOF
gnuplot temp.gp

# --- Graph (ii) ---
echo "set terminal pngcairo size 800,600 enhance font 'arial,12'" > temp.gp
echo "set output '${FOLDER}/plot_ii.png'" >> temp.gp
echo "set title 'Problem 8 (ii)'" >> temp.gp
echo "set style fill transparent solid 0.3 noborder" >> temp.gp
echo "set samples 500" >> temp.gp
echo "set size ratio -1" >> temp.gp
extract_data fii
extract_data gii
cat << 'EOF' >> temp.gp
f(x) = x**2
g(x) = -x**2
set xrange [-2:2]
plot '+' using 1:( ($1 >= -1 && $1 <= 1) ? f($1) : 1/0 ):(g($1)) with filledcurves title 'Area', \
     'Calculus/Chapter13/Problem8/fii_data.txt' using (fii_ox+fii_dx*$1):(fii_oy+fii_dy*$2) with lines linewidth 2 title 'f(x) = x^2', \
     'Calculus/Chapter13/Problem8/gii_data.txt' using (gii_ox+gii_dx*$1):(gii_oy+gii_dy*$2) with lines linewidth 2 title 'g(x) = -x^2'
EOF
gnuplot temp.gp

# --- Graph (iii) ---
echo "set terminal pngcairo size 800,600 enhance font 'arial,12'" > temp.gp
echo "set output '${FOLDER}/plot_iii.png'" >> temp.gp
echo "set title 'Problem 8 (iii)'" >> temp.gp
echo "set style fill transparent solid 0.3 noborder" >> temp.gp
echo "set samples 500" >> temp.gp
echo "set size ratio -1" >> temp.gp
extract_data fiii
extract_data giii
cat << 'EOF' >> temp.gp
f(x) = 1.0 - x**2
g(x) = x**2
set xrange [-1:1]
plot '+' using 1:( ($1 >= -1.0/sqrt(2) && $1 <= 1.0/sqrt(2)) ? f($1) : 1/0 ):(g($1)) with filledcurves title 'Area', \
     'Calculus/Chapter13/Problem8/fiii_data.txt' using (fiii_ox+fiii_dx*$1):(fiii_oy+fiii_dy*$2) with lines linewidth 2 title 'f(x) = 1 - x^2', \
     'Calculus/Chapter13/Problem8/giii_data.txt' using (giii_ox+giii_dx*$1):(giii_oy+giii_dy*$2) with lines linewidth 2 title 'g(x) = x^2'
EOF
gnuplot temp.gp

# --- Graph (iv) ---
echo "set terminal pngcairo size 800,600 enhance font 'arial,12'" > temp.gp
echo "set output '${FOLDER}/plot_iv.png'" >> temp.gp
echo "set title 'Problem 8 (iv)'" >> temp.gp
echo "set style fill transparent solid 0.3 noborder" >> temp.gp
echo "set samples 500" >> temp.gp
echo "set size ratio -1" >> temp.gp
extract_data fiv
extract_data giv
extract_data hiv
cat << 'EOF' >> temp.gp
f(x) = x**2
g(x) = 1.0 - x**2
h(x) = 2.0
bot(x) = (f(x) > g(x)) ? f(x) : g(x)
set xrange [-2:2]
plot '+' using 1:( ($1 >= -sqrt(2) && $1 <= sqrt(2)) ? h($1) : 1/0 ):(bot($1)) with filledcurves title 'Area', \
     'Calculus/Chapter13/Problem8/fiv_data.txt' using (fiv_ox+fiv_dx*$1):(fiv_oy+fiv_dy*$2) with lines linewidth 2 title 'f(x) = x^2', \
     'Calculus/Chapter13/Problem8/giv_data.txt' using (giv_ox+giv_dx*$1):(giv_oy+giv_dy*$2) with lines linewidth 2 title 'g(x) = 1 - x^2', \
     'Calculus/Chapter13/Problem8/hiv_data.txt' using (hiv_ox+hiv_dx*$1):(hiv_oy+hiv_dy*$2) with lines linewidth 2 title 'h(x) = 2'
EOF
gnuplot temp.gp

# --- Graph (v) ---
echo "set terminal pngcairo size 800,600 enhance font 'arial,12'" > temp.gp
echo "set output '${FOLDER}/plot_v.png'" >> temp.gp
echo "set title 'Problem 8 (v)'" >> temp.gp
echo "set style fill transparent solid 0.3 noborder" >> temp.gp
echo "set samples 500" >> temp.gp
echo "set size ratio -1" >> temp.gp
extract_data fv
extract_data gv
cat << 'EOF' >> temp.gp
f(x) = x**2
g(x) = x**2 - 2.0*x + 4.0
set xrange [-1:3]
plot '+' using 1:( ($1 >= 0 && $1 <= 2) ? f($1) : 1/0 ):(g($1)) with filledcurves title 'Area', \
     'Calculus/Chapter13/Problem8/fv_data.txt' using (fv_ox+fv_dx*$1):(fv_oy+fv_dy*$2) with lines linewidth 2 title 'f(x) = x^2', \
     'Calculus/Chapter13/Problem8/gv_data.txt' using (gv_ox+gv_dx*$1):(gv_oy+gv_dy*$2) with lines linewidth 2 title 'g(x) = x^2 - 2x + 4'
EOF
gnuplot temp.gp

# --- Graph (vi) ---
echo "set terminal pngcairo size 800,600 enhance font 'arial,12'" > temp.gp
echo "set output '${FOLDER}/plot_vi.png'" >> temp.gp
echo "set title 'Problem 8 (vi)'" >> temp.gp
echo "set style fill transparent solid 0.3 noborder" >> temp.gp
echo "set samples 500" >> temp.gp
echo "set size ratio -1" >> temp.gp
extract_data fvi
extract_data gvi
cat << 'EOF' >> temp.gp
f(x) = sqrt(x)
g(x) = x**2
set xrange [0:3]
plot '+' using 1:( ($1 >= 0 && $1 <= 1) ? f($1) : 1/0 ):(g($1)) with filledcurves title 'Area', \
     'Calculus/Chapter13/Problem8/fvi_data.txt' using (fvi_ox+fvi_dx*$1):(fvi_oy+fvi_dy*$2) with lines linewidth 2 title 'f(x) = sqrt(x)', \
     'Calculus/Chapter13/Problem8/gvi_data.txt' using (gvi_ox+gvi_dx*$1):(gvi_oy+gvi_dy*$2) with lines linewidth 2 title 'g(x) = x^2'
EOF
gnuplot temp.gp

# Cleanup
rm -f temp.gp
rm -f "$FOLDER"/*.gp
rm -f "$FOLDER"/*_data.txt

echo "Done generating PNG plots."
