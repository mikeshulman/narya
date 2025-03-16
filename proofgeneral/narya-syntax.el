;; narya-syntax.el --- Proof General instance for Narya - syntax file

;; We omit "display", "solve", "show", and "undo" because these should NOT appear in source files.
(defconst narya-commands
  "\\<\\(axiom\\|def\\|echo\\|synth\\|notation\\|import\\|export\\|quit\\|section\\|option\\|end\\)\\>")

;; As noted in the PG source, the default function proof-generic-state-preserving-p is not really correct; it thinks that things like "def" are state-preserving.  These are the commands that it makes sense for PG to issue directly to the prover without their being in the file.
(defun narya-state-preserving-p (cmd)
  (string-match "^echo\\|synth\\|show\\|display" cmd))

(defun narya-highlight-abstractions (limit)
  "Font-lock search function to find abstractions.
Only finds abstractions with a sequence of variables separated by
whitespace (no comments).  Finds the arguments of a simple match pattern
like \"constr. x y z ↦\", but not variables deeper inside nested or
multiple match patterns.  Unfortunately, also highlights underscores.
Does not handle sequences of abstraction variables broken across lines."
  (when (re-search-forward "[^[:word:][:space:]][[:space:]]*\\([[:word:][:space:]]+\\)\\(↦\\||->\\|⤇\\||=>\\)" limit 'move)
    ;; Move back across the ↦, so it can be the non-word-non-space character that predelimits another abstraction afterwards.
    (backward-char 1)
    t))

;; Yes, the face names here actually have to be *quoted*, even though the entire list is *also* quoted.  I think font lock expects an expression there that it *evaluates*, and while some of the faces are also variables whose value is the face of the same name, some aren't.  So we ought to quote them all.
;; Many of these regexps are simplistic and will get confused if there are comments interspersed.  They also depend on font-lock-multiline being set to t.
(defconst narya-core-font-lock-keywords
  `(
    (,narya-commands . 'font-lock-keyword-face)
    ("\\<\\(Type\\|let\\|rec\\|in\\|and\\|match\\|return\\|sig\\|data\\|codata\\|Id\\|refl\\|sym\\)\\>" . 'font-lock-builtin-face)
    ("\\<\\(all\\|id\\|none\\|only\\|except\\|renaming\\|seq\\|union\\)\\>" . 'font-lock-builtin-face)
    ("\\(axiom\\|def\\) +\\(\\w+\\)" 2 'font-lock-function-name-face)

    ;; Constructors
    ("\\<[[:word:]]+\\." . 'font-lock-constant-face) ; . is not a word-constituent, so this can't end with a \>
    ("\\<[[:digit:]]+\\>" . 'font-lock-number-face) ; these are really like constructors

    ;; Fields/methods
    ("\\.[[:word:][:digit:].]+\\>" . 'font-lock-property-name-face) ; . is not a word-constituent, so this can't begin with a \<
    ;; Field names in sig definitions.
    ("\\(sig[[:space:]\n]*(\\|,\\)[[:space:]\n]*\\([[:word:]]+\\)[[:space:]]*:" 2 'font-lock-property-name-face)
    ;; Field names in tuples.
    ("[(,][[:space:]\n]*\\([[:word:]]+\\)[[:space:]]*\\(≔\\|:=\\)" 1 'font-lock-property-name-face)

    ;; Variables bound by let-bindings
    ("\\(let[[:space:]\n]+rec\\|let\\|and\\) +\\(\\w+\\)" 2 'font-lock-variable-name-face)
    ;; Variables bound by abstractions
    (narya-highlight-abstractions 1 'font-lock-variable-name-face)
    ;; Self variables in codata declarations.
    ("[[|][[:space:]\n]*\\(\\w+\\)[[:space:]\n]*\\(↦\\||->\\)" 1 'font-lock-variable-name-face)
    ;; Variables bound in telescopes (parameters or dependent-function arguments)
    ("([[:space:]\n]*\\([[:word:][:space:]\n]+\\):" 1 'font-lock-variable-name-face)

    ;; Symbols
    ("[][(){}]" . 'font-lock-bracket-face)
    ("[→↦⤇≔~!@#$%&*/=+\\|,<>:;?-]" . 'font-lock-operator-face)
    )
  "Narya core language font-lock keywords")

(defconst narya-script-font-lock-keywords
  (append narya-core-font-lock-keywords))

(defconst narya-mode-syntax-table-entries
  (append '(?\` "< 23b")
          '(?\n "> b")
          '(?\{ "(}1nb")
          '(?\} "){4nb")
          '(?. "_")                     ; symbol constituent
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
