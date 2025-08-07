#! /bin/bash -eu

URL="https://github.com/verus-lang/verus/releases/download/release%2F0.2025.04.03.0f22710/verus-0.2025.04.03.0f22710-x86-linux.zip"
filename="verus-x86-linux"

echo "Downloading: $URL"
curl -L -o "$filename.zip" "$URL"
unzip "$filename.zip"

#cp "$filename/bin/z3" .
mv $filename verus
#rm -r "$filename"
rm "$filename.zip"

rustup install 1.82.0-x86_64-unknown-linux-gnu
