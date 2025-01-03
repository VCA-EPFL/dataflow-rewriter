#!/bin/bash
# Authors: Ayatallah Elakhras

# Input and Output files
INPUT_FILE="$1"
TEMP=$(mktemp)
OUTPUT_FILE="$2"

# Validate the arguments
if [[ -z "$INPUT_FILE" || -z "$OUTPUT_FILE" ]]; then
  echo "Usage: $0 <input_file> <output_file>"
  exit 1
fi

sh preprocess_definitions.sh $INPUT_FILE > $TEMP
sh preprocess_connections.sh $TEMP $OUTPUT_FILE
