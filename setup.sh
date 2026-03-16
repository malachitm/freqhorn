#!/bin/bash
# FreqHorn preliminary setup script
# Installs system dependencies and initializes submodules

set -e

POLAR_PYTHON_BIN="python3"


# Detect OS and install system dependencies
echo "Detecting operating system and installing system packages..."
if [ "$(uname)" = "Linux" ]; then
	# Check for Debian/Ubuntu
	if [ -f /etc/debian_version ]; then
		echo "Detected Debian/Ubuntu. Installing packages with apt-get..."
		sudo apt-get update
		sudo apt-get install -y build-essential cmake libgmp-dev libgmpxx4ldbl libboost-system-dev libarmadillo-dev python3 python3-venv python3-pip python3-setuptools gettext python-is-python3 gfortran pkg-config libopenblas-dev liblapack-dev python3-dev

		if apt-cache show python3.12 >/dev/null 2>&1 && apt-cache show python3.12-venv >/dev/null 2>&1; then
			echo "python3.12 packages are available; installing them for POLAR compatibility..."
			sudo apt-get install -y python3.12 python3.12-venv python3.12-dev
			if command -v python3.12 >/dev/null 2>&1; then
				POLAR_PYTHON_BIN="python3.12"
			fi
		else
			echo "python3.12 packages are not available in this repository (common on Debian trixie)."
			echo "Falling back to system python3 for POLAR virtual environment setup."
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
	if command -v python3.12 >/dev/null 2>&1; then
		POLAR_PYTHON_BIN="python3.12"
	fi
else
	echo "Unsupported operating system: $(uname)"
	exit 1
fi

echo "Using ${POLAR_PYTHON_BIN} for POLAR virtual environment."

echo "Initializing git submodules..."
git submodule update --init --recursive

echo "Setting up POLAR Python environment..."
if [ -d "tools/polar" ]; then
	cd tools/polar
	EXPECTED_PY_VERSION="$(${POLAR_PYTHON_BIN} -c 'import sys; print(f"{sys.version_info.major}.{sys.version_info.minor}")')"
	if [ -d ".venv" ]; then
		CURRENT_VENV_VERSION="$(.venv/bin/python3 -c 'import sys; print(f"{sys.version_info.major}.{sys.version_info.minor}")' 2>/dev/null || true)"
		if [ "${CURRENT_VENV_VERSION}" != "${EXPECTED_PY_VERSION}" ]; then
			echo "Existing tools/polar/.venv uses Python ${CURRENT_VENV_VERSION}; expected ${EXPECTED_PY_VERSION}. Recreating it..."
			rm -rf .venv
		fi
	fi
	if [ ! -d ".venv" ]; then
		${POLAR_PYTHON_BIN} -m venv .venv
	fi
	chmod +x closedforms2.py
	source .venv/bin/activate
	pip install --upgrade pip
	if [ -f "requirements.txt" ]; then
		VENV_PY_VERSION="$(python -c 'import sys; print(f"{sys.version_info.major}.{sys.version_info.minor}")')"
		if [ "${VENV_PY_VERSION}" = "3.13" ]; then
			echo "Detected Python 3.13 in POLAR virtualenv."
			echo "Installing requirements with Python-3.13-compatible scipy/numpy versions..."
			TMP_REQ_FILE="$(mktemp)"
			grep -Ev '^(scipy|numpy)==|^(scipy|numpy)~=' requirements.txt > "${TMP_REQ_FILE}"
			pip install -r "${TMP_REQ_FILE}"
			rm -f "${TMP_REQ_FILE}"
			pip install "numpy>=2.1,<2.3" "scipy>=1.14,<1.16"
		else
			pip install -r requirements.txt
		fi
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
