#!/bin/bash
# See http://stackoverflow.com/a/39769402/2314532
echo "let properties = [";
cat RRBVector.fs | grep let | grep -o "\`\`[^\`]*\`\`" | tr -d \` | awk '{printf "    \"%s\",``%s``\n", $0,$0}';
echo "]"

