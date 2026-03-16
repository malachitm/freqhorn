#!/bin/bash
# FreqHorn preliminary setup script
# Installs system dependencies and initializes submodules

set -e

POLAR_PYTHON_BIN="python3.12"
PY312_VERSION="3.12.10"
PY312_PREFIX="${HOME}/.local/python-3.12"
PY312_BIN="${PY312_PREFIX}/bin/python3.12"

install_python312_from_source() {
	echo "Installing Python ${PY312_VERSION} from python.org source..."
	TMP_BUILD_DIR="$(mktemp -d)"
	PY_TARBALL="Python-${PY312_VERSION}.tgz"
	PY_SRC_DIR="Python-${PY312_VERSION}"

	cleanup() {
		rm -rf "${TMP_BUILD_DIR}"
	}
	trap cleanup EXIT

	cd "${TMP_BUILD_DIR}"
	if command -v curl >/dev/null 2>&1; then
		curl -fsSLO "https://www.python.org/ftp/python/${PY312_VERSION}/${PY_TARBALL}"
	else
		wget "https://www.python.org/ftp/python/${PY312_VERSION}/${PY_TARBALL}"
	fi

	tar -xzf "${PY_TARBALL}"
	cd "${PY_SRC_DIR}"
	./configure --prefix="${PY312_PREFIX}" --enable-optimizations --with-ensurepip=install
	make -j"$(nproc)"
	make install

	trap - EXIT
	cleanup
}


# Detect OS and install system dependencies
echo "Detecting operating system and installing system packages..."
if [ "$(uname)" = "Linux" ]; then
	# Check for Debian/Ubuntu
	if [ -f /etc/debian_version ]; then
		echo "Detected Debian/Ubuntu. Installing packages with apt-get..."
		sudo apt-get update
		sudo apt-get install -y build-essential cmake libgmp-dev libgmpxx4ldbl libboost-system-dev libarmadillo-dev python3 python3-venv python3-pip python3-setuptools gettext python-is-python3 gfortran pkg-config libopenblas-dev liblapack-dev python3-dev \
			libssl-dev zlib1g-dev libbz2-dev libreadline-dev libsqlite3-dev libffi-dev liblzma-dev tk-dev uuid-dev curl wget xz-utils

		if command -v python3.12 >/dev/null 2>&1; then
			POLAR_PYTHON_BIN="python3.12"
		elif [ -x "${PY312_BIN}" ]; then
			POLAR_PYTHON_BIN="${PY312_BIN}"
		else
			install_python312_from_source
			if [ ! -x "${PY312_BIN}" ]; then
				echo "Failed to install Python 3.12 at ${PY312_BIN}."
				exit 1
			fi
			POLAR_PYTHON_BIN="${PY312_BIN}"
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
	if [ -x "${PY312_BIN}" ]; then
		POLAR_PYTHON_BIN="${PY312_BIN}"
	elif command -v python3.12 >/dev/null 2>&1; then
		POLAR_PYTHON_BIN="python3.12"
	else
		echo "Python 3.12 is required for POLAR. Install python@3.12 with Homebrew: brew install python@3.12"
		exit 1
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
