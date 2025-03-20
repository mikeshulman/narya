;; narya-syntax.el --- Proof General instance for Narya - syntax file

;; We omit "display", "solve", "show", and "undo" because these should NOT appear in source files.
(defconst narya-commands
  "\\_<\\(axiom\\|def\\|echo\\|synth\\|notation\\|import\\|export\\|quit\\|section\\|option\\|end\\)\\_>")

;; As noted in the PG source, the default function proof-generic-state-preserving-p is not really correct; it thinks that things like "def" are state-preserving.  These are the commands that it makes sense for PG to issue directly to the prover without their being in the file.
(defun narya-state-preserving-p (cmd)
  (string-match "^echo\\|synth\\|show\\|display" cmd))

;; TODO: Do this for everything else too.
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
    ("\\_<\\(Type\\|let\\|rec\\|in\\|and\\|match\\|return\\|sig\\|data\\|codata\\|Id\\|refl\\|sym\\)\\_>" 1 'font-lock-builtin-face)

    ;; Constants being defined.
    ("\\_<\\(axiom\\|def\\)[[:space:]\n]+\\([[:word:]_.']+\\)\\_>" 2 'font-lock-function-name-face)

    ;; Fields/methods
    ("\\_<\\.[[:word:]_.']+\\_>" . 'font-lock-property-name-face)
    ;; Field names in sig definitions.
    ("\\(\\_<sig[[:space:]\n]*(\\|,\\)[[:space:]\n]*\\([[:word:]_.']+\\)[[:space:]\n]*:" 2 'font-lock-property-name-face)
    ;; Field names in tuples.
    ("[(,][[:space:]\n]*\\([[:word:]_.']+\\)[[:space:]]*\\(≔\\|:=\\)" 1 'font-lock-property-name-face)

    ;; Constructors
    ("\\_<\\([[:word:]_.']+\\.\\)\\_>" . 'font-lock-constant-face)
    ("\\_<\\([[:digit:]]+\\)\\_>" . 'font-lock-number-face) ; these are really like constructors.

    ;; Variables bound by let-bindings
    ("\\_<\\(let[[:space:]\n]+rec\\|let\\|and\\)[[:space:]\n]+\\([[:word:]_.']+\\)\\_>" 2 'font-lock-variable-name-face)
    ;; Variables bound by abstractions
    (narya-highlight-abstractions 1 'font-lock-variable-name-face)
    ;; Self variables in codata declarations.
    ("[[|][[:space:]\n]*\\([[:word:]_.']+\\)[[:space:]\n]*\\(↦\\||->\\)" 1 'font-lock-variable-name-face)
    ;; Variables bound in telescopes (parameters or dependent-function arguments)
    ("([[:space:]\n]*\\([[:word:]_.'[:space:]\n]+\\):" 1 'font-lock-variable-name-face)

    ;; Symbols
    ("[][(){}]" . 'font-lock-bracket-face)
    ("[→↦⤇≔~!@#$%&*/=+\\|,<>:;?-]" . 'font-lock-operator-face)

    ;; "keywords" used only in import statements.  We put them last so they don't prevent other things.
    ("\\_<\\(all\\|id\\|none\\|only\\|except\\|renaming\\|seq\\|union\\)\\_>" . 'font-lock-builtin-face)
    )
  "Narya core language font-lock keywords")

(defconst narya-script-font-lock-keywords
  (append narya-core-font-lock-keywords))

(defconst narya-mode-syntax-table-entries
  (append
   ;; By default, everything can be part of a word.
   `((128 . ,(max-char)) "w")
   ;; Comments.  This is kind of black magic to deal with both block and line comments.
   '(?\` "< 23b")
   '(?\n "> b")
   '(?\{ "(}1nb")
   '(?\} "){4nb")
   ;; Whitespace
   '(?  " ")
   '(?\t " ")
   ;; Symbol constituents, which for Narya means things that can appear in identifiers like "namespace.function" or "x.01" or "long_function_name" or "f''", but which are not part of "words".  Thus an identifier can consist of multiple "words" which are moved through separately by commands like forwards-word.  That means that we can't use \< and \> in regexps to detect the beginning or end of identifiers; we have to use \_< and \_> instead.
   '(?. "_")
   '(?_ "_")
   '(?' "_")
   ;; Parentheses
   '(?( "(")
   '(?[ "(")
   '(?) ")")
   '(?] ")")
   ;; Quotes
   '(?\" "\"")
   ;; Punctuation: characters that can appear in operators (and hence mark the beginning or end of a symbol).
   '(?~ ".")
   '(?! ".")
   '(?@ ".")
   '(?# ".")
   '(?$ ".")
   '(?% ".")
   '(?& ".")
   '(?* ".")
   '(?/ ".")
   '(?= ".")
   '(?+ ".")
   '(?\ ".")
   '(?| ".")
   '(?, ".")
   '(?< ".")
   '(?> ".")
   '(?: ".")
   '(?\;  ".")
   '(?- ".")
   ;; Single-character operators are also punctuation
   '(?\? ".")
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
