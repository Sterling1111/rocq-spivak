#!/bin/sh
# Install the complete source snapshot, including scripts, plots, and documents.
set -eu
destination=$1
while IFS= read -r source; do
    install -d "$destination/$(dirname "$source")"
    mode=0644
    if test -x "$source"; then mode=0755; fi
    install -m "$mode" "$source" "$destination/$source"
done < packaging/source-files
