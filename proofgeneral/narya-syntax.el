;; narya-syntax.el --- Proof General instance for Narya - syntax file

;; We omit "display", "solve", "show", and "undo" because these should NOT appear in source files.
(defconst narya-commands
  "\\<\\(axiom\\|def\\|echo\\|synth\\|notation\\|import\\|export\\|quit\\|section\\|option\\|end\\)\\>")

;; As noted in the PG source, the default function proof-generic-state-preserving-p is not really correct; it thinks that things like "def" are state-preserving.  These are the commands that it makes sense for PG to issue directly to the prover without their being in the file.
(defun narya-state-preserving-p (cmd)
  (string-match "^echo\\|synth\\|show\\|display" cmd))

(defconst narya-core-font-lock-keywords
  `(
    (,narya-commands . font-lock-keyword-face)
    ("\\<\\(Type\\|let\\|rec\\|in\\|and\\|match\\|return\\|sig\\|data\\|codata\\|Id\\|refl\\|sym\\)\\>" . font-lock-builtin-face)
    ("\\(axiom\\|def\\) +\\(\\w+\\)" 2 font-lock-function-name-face)
    ("\\(let\\|let rec\\|and\\) +\\(\\w+\\)" 2 font-lock-variable-name-face)
    ("\\(\\(\\w \\)+\\)↦" 1 font-lock-variable-name-face)
    ("[][(){}]" . font-lock-bracket-face)
    ("[→↦⤇≔~!@#$%&*/=+\|,<>:;-?]" . font-lock-operator-face)
    ("\\<\\(\\w+\\.\\)+\\.\\>" . font-lock-constant-face)
    ("\\<\\.\\(\\w+\\.\\)+\\>" . font-lock-property-name-face)
    ("[0-9]+" . font-lock-number-face)
    )
  "Narya core language font-lock keywords")

(defconst narya-script-font-lock-keywords
  (append narya-core-font-lock-keywords))

(defconst narya-mode-syntax-table-entries
  (append '(?\` "< 23b")
          '(?\n "> b")
          '(?\{ "(}1nb")
          '(?\} "){4nb")
          '(?. "w")
          '(?_ "w")
          '(?' "w")
          `((128 . ,(max-char)) "w")
          '(?≔ ".")
          '(?⩴ ".")
          '(?→ ".")
          '(?↦ ".")
          '(?⤇ ".")
          '(?… ".")
          '(?⩲ ".")
          ))

(provide 'narya-syntax)

;; Local Variables:
;; indent-tabs-mode: nil
;; End:
