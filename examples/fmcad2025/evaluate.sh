#!/bin/bash

set -e
set -o pipefail
trap "fail 'Interrupted. Exiting.'; kill 0; exit 1" SIGINT

CONFIG_FILE="evaluate.sh.config.env"


# === Configuration ===
DEFAULT_TIMEOUT_MINUTES=60
TIMEOUT_MINUTES=$DEFAULT_TIMEOUT_MINUTES

TRIM_INTERVAL_SECONDS=60  # how often to trim
TRIM_SIZE_MB=10           # keep last 10 MB

# List of all .rab files to evaluate when using "all"
EXAMPLE_DIR="."
OUTPUT_DIR="output"
LOG_DIR="log"
ALL_RABS=("default.rab" "parameterized.rab")
# ALL_RABS=()
# for f in "${EXAMPLE_FILES[@]}"; do
#     ALL_RABS+=("${EXAMPLE_DIR}/${f}")
# done

# Path to Rabbit executable after build
RABBIT="rabbit"

RED='\033[0;31m'
YELLOW='\033[1;33m'
GREEN='\033[0;32m'
BOLD='\033[1m'
NC='\033[0m' # No Color
# === Functions ===

function timestamp() {
    date "+%Y-%m-%d %H:%M"
}
function success() {
    echo -e "${GREEN}[$(timestamp)] [✓] $*${NC}"
}

function fail() {
    echo -e "${RED}[$(timestamp)] [✗] $*${NC}"
}

function info() {
    echo -e "[$(timestamp)] [*] $*"
}

function warn() {
    echo -e "${YELLOW}[$(timestamp)] [!] $*${NC}"
}

function check_env () {
    info "Checking configuration"
    if [[ ! -f "$CONFIG_FILE" ]]; then
        fail "$CONFIG_FILE not found; try ./evaluate.sh init --docker=[none|amd64|arm64]"
        exit 1
    fi
    source "$CONFIG_FILE"

# Check TIMEOUT_CMD is defined and non-empty
if [[ -z "${TIMEOUT_CMD:-}" ]]; then
 fail "timeout command not configured correctly; try ./evaluate.sh init --docker=[none|amd64|arm64]"
  exit 1
fi

    # Check DOCKER_MODE
    case "$DOCKER_MODE" in
      arm64|amd64|none)
        success "Using --docker=$DOCKER_MODE; to reset, try ./evaluate.sh init --docker=[none|amd64|arm64]"
        ;;
      *)
        fail "rabbit executable not configured correctly; try ./evaluate.sh init --docker=[none|amd64|arm64]"
        exit 1
        ;;
    esac



}

function init() {
    for arg in "$@"; do
        case $arg in
            --docker=*) docker="${arg#*=}" ;;
            *) fail "Unknown option in init: $arg" && exit 1 ;;
        esac
    done

    echo "DOCKER_MODE=${docker:-none}" > "$CONFIG_FILE"
    # echo "[init] Config written to config.env"
    source "$CONFIG_FILE"

    info "Checking required runtime dependencies..."


    local missing=()
    local warning=()

    REQUIRED_RABBIT="rabbit"
    REQUIRED_TIMEOUT_CMDS=("timeout" "gtimeout")
    REQUIRED_PROVERIF="proverif"
    REQUIRED_TAMARIN="tamarin-prover"

    # Check for rabbit
    info "  - Checking for rabbit executable..."
    
      case "$DOCKER_MODE" in
        arm64)
            docker run --rm rabbit-artifact:arm64 echo "" >/dev/null 2>&1 || missing+=("rabbit (load arm64 docker image)")          
            ;;
        amd64)
            docker run --rm rabbit-artifact:amd64 echo "" >/dev/null 2>&1 || missing+=("rabbit (load amd64 docker image)")          
            ;;
        none)
            command -v "$REQUIRED_RABBIT" >/dev/null || missing+=("rabbit (install via: opam install .)")
            ;;
        *)
        fail "Invalid docker mode: $DOCKER_MODE"
        return 1
        ;;
      esac
    


    # Check for timeout or gtimeout
    info "  - Checking for timeout command..."
    found_timeout=false
    for cmd in "${REQUIRED_TIMEOUT_CMDS[@]}"; do
        if command -v "$cmd" >/dev/null; then
            TIMEOUT_CMD="$cmd"
            echo "TIMEOUT_CMD=${TIMEOUT_CMD}" >> "$CONFIG_FILE"
            found_timeout=true
            break
        fi
    done
    $found_timeout || missing+=("timeout (or gtimeout on macOS; try brew install coreutils)")

    # Check for tamarin-prover
    info "  - Checking for tamarin-prover..."
    command -v "$REQUIRED_TAMARIN" >/dev/null || missing+=("tamarin-prover (install via: brew install tamarin-prover/tap/tamarin-prover or build from source)")

    # Check for proverif
    info "  - Checking for proverif..."
    command -v "$REQUIRED_PROVERIF" >/dev/null || missing+=("proverif (install via: opam install proverif)")

    # Final summary
    success "Dependency check completed."

    if [ ${#missing[@]} -eq 0 ]; then
        success "All required tools are installed."
    else
        fail "Missing dependencies:"
        for dep in "${missing[@]}"; do
            echo "    - $dep"
        done
        fail "Please install the missing dependencies and rerun."
        exit 1
    fi
}

function run_measure() {
    local file=$1
    local compress=$2
    local sublemmas=$3
    local timeout_minutes=$4
    local timeout_seconds=$((timeout_minutes * 60))
    local base=${file%.rab}


    if [[ ! -f "$CONFIG_FILE" ]]; then
        fail "config file not found. Run './evaluate.sh init --docker=[none|amd64|arm64]' first."
        exit 1
    fi
    source "$CONFIG_FILE"


    mkdir -p "log"
    mkdir -p "output"

    # echo ""
    echo "=== Measuring $file with compress:$compress sub-lemmas:$sublemmas timeout:${timeout_minutes}m ==="
    # echo "[*] Running Rabbit with --compress=$compress --sub-lemmas=$sublemmas..."

    
    case "$DOCKER_MODE" in
    arm64)
      rabbit_cmd=("docker" "run" "--rm" "-v" "$(pwd):/mnt" "rabbit-artifact:arm64" "$RABBIT" "/mnt/${EXAMPLE_DIR}/${file}")      
      ;;
    amd64)
      rabbit_cmd=("docker" "run" "--rm" "-v" "$(pwd):/mnt" "rabbit-artifact:amd64" "$RABBIT" "/mnt/${EXAMPLE_DIR}/${file}")      
      ;;
    none|*)
      rabbit_cmd=("$RABBIT" "${EXAMPLE_DIR}/${file}")
      ;;
    esac

    local suffix=""
    local option=""
    if [[ "$compress" == "false" ]]; then
        rabbit_cmd+=("--compress" "false")
        option="${option} --compress false"
        suffix="${suffix}.compressed"
    fi

    if [[ "$sublemmas" == "false" ]]; then
        rabbit_cmd+=("--tag-transition" "false")
        option="${option} --tag-transition false"
        suffix="${suffix}.sublemmas"
    fi
    local spthy_file="${OUTPUT_DIR}/${base}${suffix}.spthy"
    local spthy_file_name="${base}${suffix}.spthy"

    case "$DOCKER_MODE" in
    arm64)
        rabbit_cmd+=("-o" "/mnt/$spthy_file")
        ;;
    amd64)
        rabbit_cmd+=("-o" "/mnt/$spthy_file")  
        ;;
    none|*)
        rabbit_cmd+=("-o" "$spthy_file")
        ;;
    esac





    info "Running: ${rabbit_cmd[@]}"
    "${rabbit_cmd[@]}" > /dev/null


    # echo "[*] Running tamarin-prover on ${spthy_file} proving Reachable (timeout: ${timeout_minutes}m)..."
    local LOG_FILE1="${LOG_DIR}/${spthy_file_name}.Reachable.log"
    info "Verifying Reachable Lemma for (timeout: ${timeout_minutes}m)"
    
    info "Running: $TIMEOUT_CMD "$timeout_seconds" tamarin-prover "${spthy_file}" "--prove=Reachable" &> "$LOG_FILE1"" 
    if $TIMEOUT_CMD "$timeout_seconds" tamarin-prover "${spthy_file}" "--prove=Reachable" "--quiet" &> "$LOG_FILE1"; then
        success "Tamarin terminated within timeout."
    else
        fail "Tamarin did not finish within timeout. Process was killed."   
    fi

    info "Double check the Tamarin output in $LOG_FILE1"

# 
# 

    local LOG_FILE2="${LOG_DIR}/${spthy_file_name}.Correspondence.log"
    info "Verifying Correspondence Lemma for (timeout: ${timeout_minutes}m)"
    
    info "Running: $TIMEOUT_CMD "$timeout_seconds" tamarin-prover "${spthy_file}" "--prove=Correspondence" &> "$LOG_FILE2"" 
    if $TIMEOUT_CMD "$timeout_seconds" tamarin-prover "${spthy_file}" "--prove=Correspondence" "--quiet" &> "$LOG_FILE2"; then
        success "Tamarin terminated within timeout."
    else
        fail "Tamarin did not finish within timeout. Process was killed."   
    fi

    info "Double check the Tamarin output in $LOG_FILE2"


# 
# 

    if [[ "$sublemmas" == "true" ]]; then
        local LOG_FILE3="${LOG_DIR}/${spthy_file_name}.SubLemmas.log"

        info "Verifying Sub-Lemmas for (timeout: ${timeout_minutes}m)"
        
        info "Running: $TIMEOUT_CMD "$timeout_seconds" tamarin-prover "${spthy_file}" "--prove=AlwaysStarts__" "--prove=AlwaysStartsWhenEnds__" "--prove=TransitionOnce__" &> "$LOG_FILE3"" 
        if $TIMEOUT_CMD "$timeout_seconds" tamarin-prover "${spthy_file}" "--prove=AlwaysStarts__" "--prove=AlwaysStartsWhenEnds__" "--prove=TransitionOnce__" "--quiet" &> "$LOG_FILE3"; then
            success "Tamarin terminated within timeout."
        else
            fail "Tamarin did not finish within timeout. Process was killed."   
        fi

        info "Double check the Tamarin output in $LOG_FILE3"
    fi
    echo ""

}

function measure_mode() {
    local compress="true"
    local sublemmas="true"
    source "$CONFIG_FILE"

    if [[ $1 == "all" ]]; then
        shift
        # parse global options like --timeout=...
        for arg in "$@"; do
            case $arg in
                --timeout=*) TIMEOUT_MINUTES="${arg#*=}" ;;
                *) fail "Unknown option: $arg" && exit 1 ;;
            esac
        done
        for f in "${ALL_RABS[@]}"; do
            run_measure "$f" "false" "false" "$TIMEOUT_MINUTES"
            run_measure "$f" "true" "false" "$TIMEOUT_MINUTES"
            run_measure "$f" "true" "true" "$TIMEOUT_MINUTES"
        done
    else
        local file=$1
        shift
        for arg in "$@"; do
            case $arg in
                --compress=*) compress="${arg#*=}" ;;
                --sub-lemmas=*) sublemmas="${arg#*=}" ;;
                --timeout=*) TIMEOUT_MINUTES="${arg#*=}" ;;
                *) fail "Unknown option: $arg" && exit 1 ;;
            esac
        done
        run_measure "$file" "$compress" "$sublemmas" "$TIMEOUT_MINUTES"
    fi
}

function compare_mode() {
    local timeout_minutes=$DEFAULT_TIMEOUT_MINUTES
    local timeout_seconds

    # Parse optional flags
    for arg in "$@"; do
        case $arg in
            --timeout=*) timeout_minutes="${arg#*=}" ;;
            *) fail "Unknown option in compare mode: $arg" && exit 1 ;;
        esac
    done

    timeout_seconds=$((timeout_minutes * 60))
    local spthy_file="${EXAMPLE_DIR}/default_sapicp.spthy"
    local pv_file1="output/default_sapicp.Reachable.pv"
    local pv_file2="output/default_sapicp.Correspondence.pv"
    
    local tamarin_log1="log/default_sapicp.spthy.Reachable.log"
    local tamarin_log2="log/default_sapicp.spthy.Correspondence.log"
    local proverif_log1="log/default_sapicp.spthy.Reachable.pv.log"
    local proverif_log2="log/default_sapicp.spthy.Correspondence.pv.log"

    echo "=== Running SAPIC+ with Tamarin backend ==="

    # echo "[*] Running tamarin-prover on $spthy_file proving Reachable (timeout: ${timeout_minutes}m)..."
    # echo "[*] Tamarin output will be saved to: $tamarin_log1"
    
    info "Verifying Reachable Lemma for (timeout: ${timeout_minutes}m)"
    
    info "Running: $TIMEOUT_CMD "$timeout_seconds" tamarin-prover "$spthy_file" "--prove=Reachable" &> "$tamarin_log1""    
    if $TIMEOUT_CMD "$timeout_seconds" tamarin-prover "$spthy_file" "--prove=Reachable" "--quiet" &> "$tamarin_log1"; then
        success "Tamarin terminated within timeout."
    else
        fail "Tamarin did not finish within timeout. Process was killed."
    fi
    info "Double check the Tamarin output in $tamarin_log1"

# 
# 

    info "Verifying Correspondence Lemma for (timeout: ${timeout_minutes}m)"


    info "Running: $TIMEOUT_CMD "$timeout_seconds" tamarin-prover "$spthy_file" "--prove=Correspondence" &> "$tamarin_log2""
    if $TIMEOUT_CMD "$timeout_seconds" tamarin-prover "$spthy_file" "--prove=Correspondence" "--quiet" &> "$tamarin_log2"; then
        success "Tamarin terminated within timeout."
    else
        fail "Tamarin did not finish within timeout. Process was killed."
    fi
    info "Double check the Tamarin output in $tamarin_log2"
    echo ""

    echo "=== Running ProVerif ==="

    info "Translating $spthy_file to ProVerif files: $pv_file1 and $pv_file2 "
    tamarin-prover "$spthy_file" "--lemma=Reachable" "-m=proverif" > "$pv_file1" 2>/dev/null
    tamarin-prover "$spthy_file" "--lemma=Correspondence" "-m=proverif" > "$pv_file2" 2>/dev/null

    info "Verifying Reachable Lemma for (timeout: ${timeout_minutes}m)"

    info "Running: $TIMEOUT_CMD "$timeout_seconds" proverif "$pv_file1" &> "$proverif_log1""
    if $TIMEOUT_CMD "$timeout_seconds" proverif "$pv_file1" &> "$proverif_log1"; then
        success "ProVerif terminated within timeout."
    else
        fail "ProVerif did not finish timeout. Process was killed."
    fi
    info "Double check the ProVerif output in $proverif_log1"

    # echo ""
    echo "Verifying Correspondence Lemma for (timeout: ${timeout_minutes}m)"
    echo "Running: $TIMEOUT_CMD "$timeout_seconds" proverif "$pv_file2" &> "$proverif_log2""
    if $TIMEOUT_CMD "$timeout_seconds" proverif "$pv_file2" &> "$proverif_log2"; then
        success "ProVerif terminated within timeout."
    else
        fail "ProVerif did not finish timeout. Process was killed."
    fi
    info "Double check the ProVerif output in $proverif_log2"
    echo ""
}


function trim_mode() {
    local interval=$TRIM_INTERVAL_SECONDS
    local size_mb=$TRIM_SIZE_MB

    # Parse arguments
    for arg in "$@"; do
        case $arg in
            --size=*) size_mb="${arg#*=}" ;;
            --interval=*) interval="${arg#*=}" ;;
            *) echo "Unknown option for trim: $arg" && exit 1 ;;
        esac
    done

    local size_bytes=$((size_mb * 1024 * 1024))

    echo "Watching 'log/' and trimming all files to last ${size_mb}MB every ${interval} seconds..."

    while true; do
        sleep "$interval"
        for file in log/*; do
            if [ -f "$file" ]; then
                local size=$(stat -c %s "$file" 2>/dev/null || stat -f %z "$file")
                if [ "$size" -gt "$size_bytes" ]; then
                    echo "Trimming $file (current size: $size bytes)..."
                    tail -c "$size_bytes" "$file" > "$file.tmp" && mv "$file.tmp" "$file"
                fi
            fi
        done
    done
}


# === Main entrypoint ===
case $1 in
    init)
        shift
        init "$@"
        ;;
    measure)
        shift
        check_env
        measure_mode "$@"
        ;;
    compare)
        shift
        check_env
        compare_mode "$@"
        ;;
    trim)
        shift
        trim_mode "$@"
        ;;
    *)
        echo "Usage:"
        echo "  $0 init [--docker=none|amd64|arm64]"
        # echo "  $0 measure <file.rab> [--compress=bool] [--sub-lemmas=bool] [--timeout=minutes]"
        echo "  $0 measure all [--timeout=minutes]"
        echo "  $0 compare [--timeout=minutes]"
        echo "  $0 trim [--size=Megabytes] [--interval=seconds]"
        exit 1
        ;;
esac
