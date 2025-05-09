(defvar mylang-mode-syntax-table
  (let ((st (make-syntax-table)))
    ;; OCaml-style block comments: (* ... *)
    (modify-syntax-entry ?\( "( 1" st)  ;; Opening (* starts a comment
    (modify-syntax-entry ?\* ". 23" st) ;; * is part of a comment
    (modify-syntax-entry ?\) ") 4" st)  ;; Closing *) ends a comment
    st)
  "Syntax table for MyLang.")

;; Define lists of rabbit
(defvar mylang-rabbit
  '("repeat" "case" "until" "end" "let" "in" "on" "event" "put" "skip")
  "Keywords in MyLang.")

(defvar mylang-definitions
  '("function" "equation" "constant" "syscall" "main" "process" "system" "requires" "lemma" "attack" "const" "type" "channel" "filesys" "allow" "passive" "path" "data")
  "Definition rabbit in MyLang.")

;; Convert lists to regular expressions
(defvar mylang-rabbit-regexp (regexp-opt mylang-rabbit 'words))
(defvar mylang-definitions-regexp (regexp-opt mylang-definitions 'words))

;; Define font-locking rules
(defvar mylang-font-lock-defaults
  `((,mylang-rabbit-regexp . font-lock-keyword-face)
    (,mylang-definitions-regexp . font-lock-function-name-face))
  "Highlighting rules for MyLang.")

(defun rabbit-indent-line ()
  "Indent current line in Rabbit mode."
  (interactive)
  (let ((indent-level 2))  ;; Adjust this value as needed
    (indent-line-to (* (current-indentation) indent-level))))

(setq-local tab-width 2)  ;; Set tab width to 4 spaces
(setq-local indent-tabs-mode nil)  ;; Use spaces instead of tabs (set to t for actual tab characters)

(define-derived-mode mylang-mode fundamental-mode "Rabbit"
  "Major mode for Rabbit programming language."
  :syntax-table mylang-mode-syntax-table
  (setq font-lock-defaults '(mylang-font-lock-defaults)))


(add-to-list 'auto-mode-alist '("\\.rab\\'" . mylang-mode))