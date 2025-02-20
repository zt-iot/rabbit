(setq mylang-keywords 
      '("repeat" "case" "until" "end" "let" "in" "on" "put" "skip" "event"))

(setq mylang-toplevel-keywords
      '("function" "equation" "const" "syscall" "main" "process" "system" "requires" "type" "allow" "attack"))

(setq mylang-font-lock-keywords
      `((,(regexp-opt mylang-toplevel-keywords 'words) . font-lock-function-name-face)
        (,(regexp-opt mylang-keywords 'words) . font-lock-keyword-face)
        ("(\\*\$begin:math:text$.\\\\|\\n\\$end:math:text$*?\\*)" . font-lock-comment-face))) ;; OCaml-style comments

(define-derived-mode rab-mode fundamental-mode "RabMode"
  "Major mode for my custom programming language."
  (setq font-lock-defaults '(mylang-font-lock-keywords)))

(add-to-list 'auto-mode-alist '("\\.rab\\'" . rab-mode)) ;; Adjust file extension as needed