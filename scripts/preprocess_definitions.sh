#!/bin/bash
# Authors: Ayatallah Elakhras

if [ -z "$1" ]; then
  echo "Usage: $0 <directory>"
  exit 1
fi

INPUT_FILE=$1
OUTPUT_FILE=$(mktemp)


# Function to generate a tree of Forks 
generate_fork_tree() {
  local prefix=$1 # Original Fork name
  shift           
  local outputs=("$@") 
  local forks=()       # Array to store generated fork names
  local fork_index=0

  local bbID=$(echo "$line" | grep -oP 'bbID\s*=\s*\K[^,\s]+') 
  local in=$(echo "$line" | grep -oP 'in\s*=\s*\K[^,\s]+') 
  local tagged=$(echo "$line" | grep -oP 'tagged\s*=\s*\K[^,\s]+') 
  local taggers_num=$(echo "$line" | grep -oP 'taggers_num\s*=\s*\K[^,\s]+') 
  local tagger_id=$(echo "$line" | grep -oP 'tagger_id\s*=\s*\K[^];\s]+') 

  local fixed_out_1=$(echo "${outputs[0]}" | xargs)
  local fixed_out_2=$(echo "${outputs[1]}" | xargs)

  # Process outputs in pairs
  while [ ${#outputs[@]} -gt 2 ]; do
    # Take the first two outputs
    local out1=$(echo "${outputs[0]}" | xargs)
    local out2=$(echo "${outputs[1]}" | xargs)
    outputs=("${outputs[@]:2}") # Remove the first two

    # Create a new intermediate Fork node
    local fork_name="${prefix}_$fork_index"
    forks+=("$fork_name")
    fork_index=$((fork_index + 1))

    # Write the new Fork node to the output file with clean `out` values
    echo "${fork_name} [type = \"Fork\", bbID= ${bbID}, in = ${in}, out = \"$fixed_out_1 $fixed_out_2\", tagged = ${tagged}, taggers_num = ${taggers_num}, tagger_id = ${tagger_id}];" >> "$OUTPUT_FILE"

    # Add the new Fork node to the remaining outputs
    outputs+=("$fork_name")
  done

  # Handle the final Fork node
  if [ ${#outputs[@]} -eq 2 ]; then
    # Clean the `out` field values and reuse the original Fork name
    local out1=$(echo "${outputs[0]}" | xargs)
    local out2=$(echo "${outputs[1]}" | xargs)
    echo "${prefix} [type = \"Fork\", bbID= ${bbID}, in = ${in}, out = \"$fixed_out_1 $fixed_out_2\", tagged = ${tagged}, taggers_num = ${taggers_num}, tagger_id = ${tagger_id}];" >> "$OUTPUT_FILE"
  else
    outputs+=("${outputs[0]}")
  fi

  # Return the generated fork names
  echo "${forks[@]}"
}

# Main function to process the file
process_file() {
  while IFS= read -r line; do

    if echo "$line" | grep -q '\[type = "Fork"'; then
      # Extract the name and outputs
      fork_name=$(echo "$line" | grep -o '^[^ ]*') # Get the Fork name
      outputs=$(echo "$line" | grep -o 'out = ".*"' | sed -E 's/out = "(.*)"/\1/')
      IFS=' ' read -ra out_array <<<"$outputs"

      # Check if the Fork has more than two outputs
      if [ ${#out_array[@]} -gt 2 ]; then
        # Generate a tree of Forks, keeping the original Fork name
        forks+=$(generate_fork_tree "$fork_name" "${out_array[@]}")
      else
        # If the Fork has exactly two outputs, just write it as is
        echo "$line" >> "$OUTPUT_FILE"
      fi
    else
       # Write non-Fork lines unchanged
      echo "$line" >> "$OUTPUT_FILE"
   
    fi
  done <"$INPUT_FILE"

}


process_file
 # Perform the post-processing to fix the incorrect format and types
sed 's/_"\([0-9]\)/_\1/g' "$OUTPUT_FILE" | sed 's/\([0-9]\)"_\([0-9]\)/\1_\2"/g' | sed 's/"Fork"/"fork Bool 2"/g' | sed 's/"Mux"/"mux T"/g'| sed 's/"Branch"/"branch T"/g' 