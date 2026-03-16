#!/bin/bash
# FreqHorn preliminary setup script
# Installs system dependencies and initializes submodules

set -e

# System dependencies (Debian/Ubuntu)
echo "Installing system packages..."
sudo apt-get update
sudo apt-get install -y build-essential cmake libgmp-dev libgmpxx4ldbl libboost-system-dev libarmadillo-dev python3 python3-venv python3-pip

echo "Initializing git submodules..."
git submodule update --init --recursive

echo "Setting up POLAR Python environment..."
if [ -d "tools/polar" ]; then
	cd tools/polar
	if [ ! -d ".venv" ]; then
		python3 -m venv .venv
	fi
	source .venv/bin/activate
	pip install --upgrade pip
	if [ -f "requirements.txt" ]; then
		pip install -r requirements.txt
	fi
	deactivate
	cd - > /dev/null
	echo "POLAR Python environment setup complete."
else
	echo "tools/polar directory not found. Please check your submodules."
fi

echo "FreqHorn preliminary setup complete."
echo "Next steps:"
echo "- Build FreqHorn using CMake and Make (see README)"
