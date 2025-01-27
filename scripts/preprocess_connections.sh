#!/bin/bash
# Authors: Ayatallah Elakhras

fix_fork_connections() {
  local prefix=$1
  local fork_index=0

  IFS=$'\n' read -d '' -r -a outputs < <(grep -P "\"$fork_name\" ->" "$INPUT_FILE")

  while [ ${#outputs[@]} -gt 2 ]; do
    local out1=$(echo "${outputs[0]}") 
    local out2=$(echo "${outputs[1]}")

    local dest1=$(echo "$out1" | grep -oP '(?<=-> )\S+(?= \[)')
    local dest2=$(echo "$out2" | grep -oP '(?<=-> )\S+(?= \[)')
    if [[ -z "$dest1" ]]; then
      dest1="\"${out1}\""
    fi

    if [[ -z "$dest2" ]]; then
      dest2="\"${out2}\""
    fi

    local color1=$(echo "$out1" | grep -oP '(?<=color = )\S+(?=,)')
    local color2=$(echo "$out2" | grep -oP '(?<=color = )\S+(?=,)')
    if [[ -z "$color1" ]]; then
      color1="\"gold3\""
    fi

    if [[ -z "$color2" ]]; then
      color2="\"gold3\""
    fi

    local to1=$(echo "$out1" | grep -oP '(?<=to = )\S+(?=])')
    local to2=$(echo "$out2" | grep -oP '(?<=to = )\S+(?=])')
    if [[ -z "$to1" ]]; then
      to1="\"in1\""
    fi

    if [[ -z "$to2" ]]; then
      to2="\"in1\""
    fi

    outputs=("${outputs[@]:2}") # Remove the first two

    # Create a new intermediate Fork node
    local fork_name="${prefix}_$fork_index"
    forks+=("$fork_name")
    fork_index=$((fork_index + 1))

    echo "    \"${fork_name}\" -> ${dest1} [color = ${color1}, from = \"out1\", to = ${to1}];" >> "$OUTPUT_FILE"
    echo "    \"${fork_name}\" -> ${dest2} [color = ${color2}, from = \"out2\", to = ${to2}];" >> "$OUTPUT_FILE"

    # Add the new Fork node to the remaining outputs
    outputs+=("$fork_name")

  done

  # Handle the final Fork node
  if [ ${#outputs[@]} -eq 2 ]; then
    # Clean the `out` field values and reuse the original Fork name
    local out1=$(echo "${outputs[0]}" | xargs)
    local out2=$(echo "${outputs[1]}" | xargs)

    local dest1=$(echo "$out1" | grep -oP '(?<=-> )\S+(?= \[)')
    local dest2=$(echo "$out2" | grep -oP '(?<=-> )\S+(?= \[)')
    if [[ -z "$dest1" ]]; then
      dest1="\"${out1}\""
    fi

    if [[ -z "$dest2" ]]; then
      dest2="\"${out2}\""
    fi

    local color1=$(echo "$out1" | grep -oP '(?<=color = )\S+(?=,)')
    local color2=$(echo "$out2" | grep -oP '(?<=color = )\S+(?=,)')
    if [[ -z "$color1" ]]; then
      color1="\"gold3\""
    fi

    if [[ -z "$color2" ]]; then
      color2="\"gold3\""
    fi

    local to1=$(echo "$out1" | grep -oP '(?<=to = )\S+(?=])')
    local to2=$(echo "$out2" | grep -oP '(?<=to = )\S+(?=])')
    if [[ -z "$to1" ]]; then
      to1="\"in1\""
    fi

    if [[ -z "$to2" ]]; then
      to2="\"in1\""
    fi

    echo "    \"${prefix}\" -> ${dest1} [color = ${color1}, from = \"out1\", to = ${to1}];" >> "$OUTPUT_FILE"
    echo "    \"${prefix}\" -> ${dest2} [color = ${color2}, from = \"out2\", to = ${to2}];" >> "$OUTPUT_FILE"
  else
    outputs+=("${outputs[0]}")
  fi
}

# Function to parse the input file and extract relevant fork connections
parse_input() {
  local old_fork_name="None"
  while IFS= read -r line; do
    # Match lines with forks and their connections
    if [[ "$line" =~ .*fork.*.*-\>.* ]]; then
      fork_name=$(echo "$line" | sed -n 's/.*"\([^\"]*\)" ->.*/\1/p')

      IFS=$'\n' read -d '' -r -a outputs < <(grep -F "\"$fork_name\" ->" "$INPUT_FILE")

      if [ "$fork_name" == "$old_fork_name" ]; then
        if [ ${#outputs[@]} -gt 2 ]; then
          continue
        fi
      fi


      if [ ${#outputs[@]} -gt 2 ]; then
       # Process the fork if it's a multi-output fork
        fix_fork_connections "$fork_name" 
      else
        echo "$line" >> "$OUTPUT_FILE"
      fi
      
    else
      # Write non-matching lines unchanged
      echo "$line" >> "$OUTPUT_FILE"
    fi
    old_fork_name=$fork_name
  done < "$INPUT_FILE"
}

# Input and Output files
INPUT_FILE="$1"
OUTPUT_FILE="$2"

# Validate the arguments
if [[ -z "$INPUT_FILE" || -z "$OUTPUT_FILE" ]]; then
  echo "Usage: $0 <input_file> <output_file>"
  exit 1
fi

# Create or clear the output file
> "$OUTPUT_FILE"

# Parse the input file and process forks
parse_input
