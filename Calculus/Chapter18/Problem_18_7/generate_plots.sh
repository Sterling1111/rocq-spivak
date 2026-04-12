#!/bin/bash
# Navigate to the root directory of the Coq project
cd "$(dirname "$0")/../../.." || exit

FOLDER="Calculus/Chapter18/Problem_18_7"
COQ_FILE="Calculus/Chapter18/Problem_18_7.v"
VO_FILE="Calculus/Chapter18/Problem_18_7.vo"

echo "Cleaning up $FOLDER..."
mkdir -p "$FOLDER"
# Avoid deleting the script itself
find "$FOLDER" -type f ! -name 'generate_plots.sh' -delete

# Force re-compilation to generate .gp plots
echo "Compiling $COQ_FILE to generate .gp plots..."
rm -f "$VO_FILE"
coqc -w "-deprecated-dirpath-Coq,-deprecated-since-9.0" -R Lib Lib -R Calculus Calculus -R ATTAM ATTAM -I src "$COQ_FILE"

# Generate PNG plots from any existing .gp files
shopt -s nullglob
for f in "$FOLDER"/*.gp; do
    base=$(basename "$f" .gp)
    
    # Map the filename to its function equation for the title
    case $base in
        sinh) func="sinh(x) = (e^{x} - e^{-x}) / 2" ; func_label="(e^{x} - e^{-x}) / 2" ;;
        cosh) func="cosh(x) = (e^{x} + e^{-x}) / 2" ; func_label="(e^{x} + e^{-x}) / 2" ;;
        tanh) func="tanh(x) = (e^{x} - e^{-x}) / (e^{x} + e^{-x})" ; func_label="(e^{x} - e^{-x}) / (e^{x} + e^{-x})" ;;
        *)  func="$base(x)" ; func_label="$base(x)" ;;
    esac
    
    temp_gp="temp_${base}.txt"
    echo "set terminal pngcairo size 800,600 enhance font 'arial,12'" > "$temp_gp"
    echo "set output '${FOLDER}/${base}.png'" >> "$temp_gp"
    echo "set title '${func}'" >> "$temp_gp"
    echo "set size ratio -1" >> "$temp_gp"
    
    if [ "$base" = "tanh" ]; then
        echo "set key top left" >> "$temp_gp"
    fi
    
    # Overwrite 'notitle' to bring back the legend box
    # To make line thicknesses match perfectly in the legend and plot, we swap the generated 'filledcurves' for 'lines linewidth 2'
    sed "s|notitle with filledcurves|title '${func_label}' with lines linewidth 2|" "$f" | grep -v "pause mouse" >> "$temp_gp"
    
    gnuplot "$temp_gp"
    rm -f "$temp_gp"
    echo "Generated ${base}.png"
done

# Cleanup .gp files
rm -f "$FOLDER"/*.gp
echo "Done! Removed .gp files."
