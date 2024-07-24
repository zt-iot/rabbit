


;;; spthy.el --- SPTHY major mode
;; Author: Katriel Cohn-Gordon

;; PRE-TAMARIN MODE: [UGLY HACK] this mode is only used to be able to highlight comments '//' AND  '/* */'
;;                   since 'modify-syntax-entry' seems unable to deal with both types of comments :(
(require 'generic-x)
(define-generic-mode
  'pre-rab-mode
  '( ("(*" . "*)"))  ;; C-like comments
  '()
  '(((rx "X" (group (any ascii)) "X") . 'font-lock-keyword-face))
  '("\\.rab$") ;; files for which to activate this mode
  nil            ;; other functions to call
  "A mode for Tamarin files") ;; doc string for this mode

;; TAMARIN-MODE
;; Keybindings
(defvar rab-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\C-j" 'newline-and-indent)
    map)
  "Keymap for RAB major mode")

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.rab\\'" . rab-mode))

(defvar rab-operators
  '("&" "|" "==>" "=" "<=>" "-->" "^" "[" "]->" "-->" "]" "--[" "->" "=>"))

(defconst rab-font-lock-keywords-1
  (list
   '("\\<\\(for\\|if\\|let\\|return\\|with\\)\\>" . font-lock-keyword-face)
   '("\\<\\(channel\\|filesys\\|process\\|system\\|requires\\|lemma\\)\\>" . font-lock-constant-face)
   '("\\<\\(@\\|a\\(?:llow\\|ttack\\)\\|constant\\|e\\(?:quation\\|xternal\\)\\|function\\|main\\|syscall\\|type\\)\\>" . font-lock-warning-face)
   '("\\(-\\(?:-[>[]\\|>\\)\\|\\(?:<=\\|==?\\|]-\\)>\\|[]&=[|^]\\)" . font-lock-constant-face)
   )
   "Minimal highlighting expressions for RAB mode")


(define-derived-mode rab-mode pre-rab-mode "RAB"
  "Major mode for editing Tamarin's RAB files."
  
  ;; Fontify keywords
  (setq font-lock-defaults '(rab-font-lock-keywords-1))

  (modify-syntax-entry ?_ "w" rab-mode-syntax-table)

  ;; < > are delimiters too
  (modify-syntax-entry ?< "(" rab-mode-syntax-table)
  (modify-syntax-entry ?> "(" rab-mode-syntax-table)
  
  ;; { } are delimiters too
  (modify-syntax-entry ?{ "(" rab-mode-syntax-table)
  (modify-syntax-entry ?} "(" rab-mode-syntax-table)

  )

(provide 'rab-mode)
