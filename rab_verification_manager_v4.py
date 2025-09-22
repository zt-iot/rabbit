#!/usr/bin/env python3
"""
RAB Verification Manager - Main tool for managing .rab compilation and verification
"""

import json
import os
import subprocess
import argparse
import hashlib
import time
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple
from dataclasses import dataclass, asdict
import logging

# Configure logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)


default_rab_compiler = "_build/default/src/rabbit.exe"

@dataclass
class CompilationConfig:
    """Represents a compilation configuration"""
    name: str
    flags: List[str]
    
    @classmethod
    def from_flags(cls, flags: List[str]) -> 'CompilationConfig':
        """Create config from flags list"""
        flag_names = []
        for flag in flags:
            if flag == '--tag-transition':
                flag_names.append('tag-transition')
            elif flag == '--post-process':
                flag_names.append('post-process')
        
        name = '_'.join(flag_names) if flag_names else 'no_flags'
        return cls(name=name, flags=flags)

    def __str__(self):
        res = ""
        for flag in self.flags:
            if flag == '--tag-transition':
                res += "_tt"
            elif flag == '--post-process':
                res += "_pp"
        return res

    

@dataclass
class LemmaResult:
    """Result of a single lemma verification"""
    status: str  # "proven", "disproven", "timeout", "error"
    time: float
    details: Optional[str] = None

@dataclass
class RunResult:
    """Result of a lemma subset run"""
    run_id: str
    status: str  # "completed", "failed", "timeout"
    lemma_results: Dict[str, LemmaResult]
    total_time: float
    tamarin_version: Optional[str]
    timestamp: str
    
class RABManager:
    """Main manager class for RAB verification workflow"""
    
    def __init__(self, results_dir: str = "results"):
        self.results_dir = Path(results_dir)
        self.results_dir.mkdir(exist_ok=True)
        self.config_metadata_file = self.results_dir / "config_metadata.json"
        self.global_summary_file = self.results_dir / "global_summary.json"
        
        # Initialize metadata if it doesn't exist
        self._init_config_metadata()
    
    def _init_config_metadata(self):
        """Initialize configuration metadata file"""
        default_configs = {
            "no_flags": {"flags": []},
            "tag-transition": {"flags": ["--tag-transition"]},
            "post-process": {"flags": ["--post-process"]},
            "tag-transition_post-process": {"flags": ["--tag-transition", "--post-process"]}
        }
        
        if not self.config_metadata_file.exists():
            with open(self.config_metadata_file, 'w') as f:
                json.dump(default_configs, f, indent=2)
    
    def get_rab_file_dir(self, rab_file: str) -> Path:
        """Get directory for a specific .rab file"""
        rab_name = Path(rab_file).stem
        return self.results_dir / rab_name
    
    def get_compilation_dir(self, rab_file: str, config: CompilationConfig) -> Path:
        """Get directory for a specific compilation configuration"""
        return self.get_rab_file_dir(rab_file) / config.name
    
    def get_lemma_run_dir(self, rab_file: str, config: CompilationConfig, lemma_subset_name: str) -> Path:
        """Get directory for a specific lemma run"""
        return self.get_compilation_dir(rab_file, config) / "lemma_runs" / lemma_subset_name
    
    def compile_rab(self, rab_file: str, config: CompilationConfig, compiler_path: str = default_rab_compiler) -> bool:
        """Compile a .rab file with given configuration"""
        compilation_dir = self.get_compilation_dir(rab_file, config)
        compilation_dir.mkdir(parents=True, exist_ok=True)
        
        output_file = compilation_dir / "compiled.spthy"
        log_file = compilation_dir / "compilation_log.txt"
        
        # Build command
        cmd = [compiler_path] + config.flags + [rab_file, "-o", str(output_file)]
        
        logger.info(f"Compiling {rab_file} with config {config.name}")
        logger.info(f"Command: {' '.join(cmd)}")
        
        try:
            with open(log_file, 'w') as log:
                result = subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT, 
                                      text=True, timeout=300)  # 5 minute timeout
                
            if result.returncode == 0:
                logger.info(f"Compilation successful: {output_file}")
                return True
            else:
                logger.error(f"Compilation failed with return code {result.returncode}")
                return False
                
        except subprocess.TimeoutExpired:
            logger.error("Compilation timed out")
            return False
        except Exception as e:
            logger.error(f"Compilation error: {e}")
            return False
    
    def run_lemma_verification(self, rab_file: str, config: CompilationConfig, 
                             lemma_subset_name: str, lemmas: List[str], 
                             tamarin_path: str = "tamarin-prover", timeout: int = 3600) -> RunResult:
        """Run verification for a subset of lemmas"""
        
        run_dir = self.get_lemma_run_dir(rab_file, config, lemma_subset_name)
        run_dir.mkdir(parents=True, exist_ok=True)
        
        spthy_file = self.get_compilation_dir(rab_file, config) / "compiled.spthy"
        if not spthy_file.exists():
            raise FileNotFoundError(f"Compiled file not found: {spthy_file}")
        
        # Generate unique run ID
        run_id = hashlib.md5(f"{rab_file}_{config.name}_{lemma_subset_name}_{time.time()}".encode()).hexdigest()[:8]
        
        # Build Tamarin command
        if lemmas:
            # Run specific lemmas: tamarin-prover --prove=lemma1,lemma2,lemma3 file.spthy
            lemma_list = ",".join(lemmas)
            tamarin_args = ["--prove=" + lemma_list]
        else:
            # Run all lemmas: tamarin-prover --prove file.spthy
            tamarin_args = ["--prove"]
        
        # Save run configuration
        run_config = {
            "lemmas": lemmas if lemmas else "all",
            "timestamp": datetime.now().isoformat(),
            "tamarin_args": tamarin_args,
            "timeout": timeout
        }
        
        with open(run_dir / "run_config.json", 'w') as f:
            json.dump(run_config, f, indent=2)
        
        # Run Tamarin once for all lemmas
        logger.info(f"Verifying lemmas: {lemmas if lemmas else 'all'}")
        total_start_time = time.time()
        
        cmd = [tamarin_path] + tamarin_args + [str(spthy_file)]
        
        output_file = run_dir / ("tamarin_output" + str(config) + ".txt")
        
        try:
            with open(output_file, 'w') as outf:
                result = subprocess.run(cmd, stdout=outf, stderr=subprocess.STDOUT, 
                                      text=True, timeout=timeout)
            
            total_time = time.time() - total_start_time
            
            lemma_results = {}
            
            if result.returncode == 0:
                run_status = "completed"
            else:
                run_status = "failed"
                
        except subprocess.TimeoutExpired:
            total_time = time.time() - total_start_time
            run_status = "timeout"
            # Create timeout results for all lemmas
            if lemmas:
                lemma_results = {lemma: LemmaResult(status="timeout", time=total_time/len(lemmas)) for lemma in lemmas}
            else:
                # If no specific lemmas, we can't know which ones timed out without parsing
                lemma_results = {"unknown": LemmaResult(status="timeout", time=total_time)}
            logger.warning("Tamarin verification timed out")
        
        except Exception as e:
            total_time = time.time() - total_start_time
            run_status = "error"
            error_msg = str(e)
            if lemmas:
                lemma_results = {lemma: LemmaResult(status="error", time=0, details=error_msg) for lemma in lemmas}
            else:
                lemma_results = {"unknown": LemmaResult(status="error", time=0, details=error_msg)}
            logger.error(f"Tamarin verification error: {e}")
        
        total_time = time.time() - total_start_time
        
        # Get Tamarin version
        tamarin_version = self._get_tamarin_version(tamarin_path)
        
        # Create result object
        run_result = RunResult(
            run_id=run_id,
            status="completed",
            lemma_results=lemma_results,
            total_time=total_time,
            tamarin_version=tamarin_version,
            timestamp=datetime.now().isoformat()
        )
        
        # Save results
        # self._save_run_result(run_dir, run_result)
        
        return run_result
    
    def _get_tamarin_version(self, tamarin_path: str) -> Optional[str]:
        """Get Tamarin version"""
        try:
            result = subprocess.run([tamarin_path, "--version"], capture_output=True, text=True, timeout=10)
            if result.returncode == 0:
                return result.stdout.strip()
        except Exception:
            pass
        return None
    
    def _save_run_result(self, run_dir: Path, result: RunResult):
        """Save run result to JSON"""
        result_dict = asdict(result)
        with open(run_dir / "results_summary.json", 'w') as f:
            json.dump(result_dict, f, indent=2)
    
    def update_global_summary(self):
        """Update the global summary with all results"""
        summary = {
            "last_updated": datetime.now().isoformat(),
            "files": {}
        }
        
        for rab_dir in self.results_dir.iterdir():
            if rab_dir.is_dir() and rab_dir.name not in ["config_metadata.json", "global_summary.json"]:
                rab_name = rab_dir.name
                summary["files"][f"{rab_name}.rab"] = self._summarize_rab_results(rab_dir)
        
        with open(self.global_summary_file, 'w') as f:
            json.dump(summary, f, indent=2)
    
    def _summarize_rab_results(self, rab_dir: Path) -> Dict:
        """Summarize results for a single .rab file"""
        file_summary = {"compilations": {}}
        
        for config_dir in rab_dir.iterdir():
            if config_dir.is_dir():
                config_name = config_dir.name
                file_summary["compilations"][config_name] = self._summarize_config_results(config_dir)
        
        return file_summary
    
    def _summarize_config_results(self, config_dir: Path) -> Dict:
        """Summarize results for a compilation configuration"""
        config_summary = {"lemma_runs": {}}
        lemma_runs_dir = config_dir / "lemma_runs"
        
        if lemma_runs_dir.exists():
            for run_dir in lemma_runs_dir.iterdir():
                if run_dir.is_dir():
                    run_name = run_dir.name
                    results_file = run_dir / "results_summary.json"
                    
                    if results_file.exists():
                        try:
                            with open(results_file) as f:
                                run_data = json.load(f)
                            
                            # Summarize lemma results
                            proven = sum(1 for r in run_data["lemma_results"].values() if r["status"] == "proven")
                            disproven = sum(1 for r in run_data["lemma_results"].values() if r["status"] == "disproven")
                            timeout = sum(1 for r in run_data["lemma_results"].values() if r["status"] == "timeout")
                            error = sum(1 for r in run_data["lemma_results"].values() if r["status"] == "error")
                            
                            config_summary["lemma_runs"][run_name] = {
                                "status": run_data["status"],
                                "proven": proven,
                                "disproven": disproven,
                                "timeout": timeout,
                                "error": error,
                                "total_time": run_data["total_time"]
                            }
                            
                        except Exception as e:
                            logger.error(f"Error processing results in {results_file}: {e}")
                            config_summary["lemma_runs"][run_name] = {"status": "error", "error": str(e)}
        
        return config_summary

def main():
    parser = argparse.ArgumentParser(description="RAB Verification Manager")
    parser.add_argument("command", choices=["compile", "verify", "summary"], 
                       help="Command to execute")
    parser.add_argument("--rab-file", required=True, help="Path to .rab file")
    parser.add_argument("--config", help="Compilation config name (default: no_flags)")
    parser.add_argument("--flags", nargs="*", help="Compilation flags")
    parser.add_argument("--lemmas", nargs="*", help="Lemmas to verify")
    parser.add_argument("--compiler", default=default_rab_compiler, help="Path to RAB compiler")
    parser.add_argument("--tamarin", default="tamarin-prover", help="Path to Tamarin prover")
    parser.add_argument("--timeout", type=int, default=3600, help="Timeout per lemma (seconds)")
    parser.add_argument("--results-dir", default="results", help="Results directory")
    
    args = parser.parse_args()
    
    manager = RABManager(args.results_dir)
    
    if args.command == "compile":
        if args.config:
            # Use named config
            with open(manager.config_metadata_file) as f:
                configs = json.load(f)
            if args.config not in configs:
                logger.error(f"Unknown config: {args.config}")
                return 1
            config = CompilationConfig(name=args.config, flags=configs[args.config]["flags"])
        else:
            # Use flags directly
            flags = args.flags or []
            config = CompilationConfig.from_flags(flags)
        
        success = manager.compile_rab(args.rab_file, config, args.compiler)
        return 0 if success else 1
    
    elif args.command == "verify":
        if not args.config:
            args.config = "no_flags"
        
        with open(manager.config_metadata_file) as f:
            configs = json.load(f)
        config = CompilationConfig(name=args.config, flags=configs[args.config]["flags"])
        
        lemmas = args.lemmas or []  # Empty list if no lemmas specified
        if not lemmas:
            subset_name = "default"
        else:
            subset_name = "__".join(args.lemmas)
        
        # If no lemmas provided, we'll run all lemmas (handled in run_lemma_verification)
        if not lemmas:
            logger.info("No specific lemmas provided. Will verify all lemmas in the file.")
        
        try:
            result = manager.run_lemma_verification(
                args.rab_file, config, subset_name, lemmas, args.tamarin, args.timeout
            )
            logger.info(f"Verification completed. Run ID: {result.run_id}")
            manager.update_global_summary()
            return 0
        except Exception as e:
            logger.error(f"Verification failed: {e}")
            return 1
    
    elif args.command == "summary":
        manager.update_global_summary()
        with open(manager.global_summary_file) as f:
            summary = json.load(f)
        print(json.dumps(summary, indent=2))
        return 0

if __name__ == "__main__":
    exit(main())