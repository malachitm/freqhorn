#!/bin/bash
# FreqHorn preliminary setup script
# Installs system dependencies and initializes submodules

set -e


# Detect OS and install system dependencies
echo "Detecting operating system and installing system packages..."
if [ "$(uname)" = "Linux" ]; then
	# Check for Debian/Ubuntu
	if [ -f /etc/debian_version ]; then
		echo "Detected Debian/Ubuntu. Installing packages with apt-get..."
		sudo apt-get update
		sudo apt-get install -y build-essential cmake libgmp-dev libgmpxx4ldbl libboost-system-dev libarmadillo-dev python3 python3-venv python3-pip python3-setuptools gettext python-is-python3 gfortran pkg-config libopenblas-dev liblapack-dev python3-dev python3.12 python3.12-venv python3.12-dev

		if ! command -v python3.12 >/dev/null 2>&1; then
			echo "python3.12 was not found after installation attempt."
			echo "Please enable the appropriate repository for your distro and install: python3.12 python3.12-venv python3.12-dev"
			exit 1
		fi
	else
		echo "Linux distribution not automatically supported. Please install dependencies manually."
		exit 1
	fi
elif [ "$(uname)" = "Darwin" ]; then
	echo "Detected macOS. Installing packages with Homebrew..."
	if ! command -v brew >/dev/null 2>&1; then
		echo "Homebrew not found. Installing Homebrew..."
		/bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
		eval "$($(brew --prefix)/bin/brew shellenv)"
	fi
	brew update
	brew install cmake gmp boost armadillo python3
	# Recommend Xcode command line tools
	if ! xcode-select -p >/dev/null 2>&1; then
		echo "Installing Xcode command line tools..."
		xcode-select --install
	fi
else
	echo "Unsupported operating system: $(uname)"
	exit 1
fi

echo "Initializing git submodules..."
git submodule update --init --recursive

echo "Setting up POLAR Python environment..."
if [ -d "tools/polar" ]; then
	cd tools/polar
	if [ -d ".venv" ]; then
		if ! .venv/bin/python3 -c "import sys; raise SystemExit(0 if (sys.version_info.major == 3 and sys.version_info.minor == 12) else 1)" >/dev/null 2>&1; then
			echo "Existing tools/polar/.venv is not Python 3.12; recreating it..."
			rm -rf .venv
		fi
	fi
	if [ ! -d ".venv" ]; then
		python3.12 -m venv .venv
	fi
	chmod +x closedforms2.py
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
