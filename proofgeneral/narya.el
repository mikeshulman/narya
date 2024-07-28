;;;narya.el --- Proof General instance for Narya

(eval-and-compile
  (require 'proof-site)  
  (require 'pg-custom)                
  (require 'proof)
  (require 'proof-easy-config)	
  (proof-ready-for-assistant 'narya))        ;; compilation for narya

(require 'narya-syntax)
(require 'font-lock)

;; Add a formfeed at the end of the command, as a delimiter for PG-interaction-mode
(defun narya-script-preprocess (file start end cmd)
	(list (concat cmd "\n\x0C\n")))

;; Easy configuration
(proof-easy-config 
 ;; The two names below should be the same as in proof-site.el
   'narya "Narya"      
   proof-prog-name                       "narya"
   narya-prog-args                       `("-proofgeneral")
   proof-toolbar-enable                  t
 
	 ;; when not nil, a space is added to the beginning of the previous line at each new line transition.
   narya-script-indent                   nil  
 
	 ;; Syntax and font-lock
   proof-script-syntax-table-entries     narya-mode-syntax-table-entries
   proof-script-font-lock-keywords       narya-script-font-lock-keywords
   proof-goals-font-lock-keywords        narya-script-font-lock-keywords
   proof-response-font-lock-keywords     narya-script-font-lock-keywords
 
	 ;; Comment syntax
   proof-script-comment-start            "`"       ;; For line comments
   proof-script-comment-end              ""        ;; For line comments
	 ;; So far, it appears that it really does work for these two to be separately disjunctive.
   proof-script-comment-start-regexp     "{`\\|`"  ;; Matches either block or line comment start
   proof-script-comment-end-regexp       "`}\\|\n" ;; Matches either block comment end or newline for line comments
   proof-script-fly-past-comments        t         ;; Ignores comments during processing and navigation
	 comment-quote-nested                  nil			 ;; Nested comments are allowed
 
	 ;; Commands
   proof-script-command-start-regexp     narya-commands

	 ;; Undo
	 proof-non-undoables-regexp            "undo"
	 proof-ignore-for-undo-count           "echo\\|show\\|undo"
	 proof-undo-n-times-cmd                "undo %s\n\x0C" ;; has to end with a formfeed to terminate a PG-mode command
	 proof-state-preserving-p              'narya-state-preserving-p
	 ;; The difference between proof-count-undos-fn and proof-find-and-forget-fn seems to be that the former is called iff staying inside a single proof.  However, as far as I can see, for Narya the default value of the former also works for the latter.
	 proof-find-and-forget-fn              'proof-generic-count-undos

	 ;; multiple file management
	 proof-no-fully-processed-buffer       t
	 ;; TODO: more?

	 ;; Delimiting input commands
	 ;; Narya allows internal CR in interactive command, and has line-comments ended by CR that could appear internally to a command, so we *have* to leave the CRs in place.  The preprocessing function adds a formfeed as an end-of-command marker instead.
	 proof-shell-strip-crs-from-input      nil
	 proof-script-preprocess               'narya-script-preprocess
 ;; This won't get used for parsing commands since proof-script-command-start-regexp takes priority, but it will get added automatically to the end of minibuffer-read commands.
	 proof-terminal-string                 "\n\x0C\n"
	 proof-shell-auto-terminate-commands   t

	 ;; Silencing unnecessary output (TODO)
	 ;proof-shell-start-silent-cmd          ""
	 ;proof-shell-stop-silent-cmd           ""

	 ;; Parsing output
	 ;; The PG-mode prompt doesn't need to be human-readable or writeable, so we use formfeed characters to ensure no accidental collisions with ordinary output.
   proof-shell-annotated-prompt-regexp   "\x0C\\[narya\\]\x0C"
   proof-shell-error-regexp              "^ ￫ \\(error\\|bug\\)"
	 proof-shell-truncate-before-error     nil

	 ;; interactive proof (TODO)
	 ;proof-shell-proof-completed-regexp    ""
	 ;proof-shell-start-goals-regexp        ""
	 ;proof-shell-end-goals-regexp          ""

	 ;; Settings for generic user-level commands
   proof-assistant-home-page             "https://github.com/mikeshulman/narya/"
)

;; The Emacs comment functions are a bit weird and inconsistent.
;; comment-dwim (M-;) checks if the line is empty.
;; - if the line is empty:
;;   - if comment-insert-comment-function is non-nil, it calls that.
;;   - otherwise, it directly inserts comment-start and comment-end.
;; - if the line is not empty, it calls comment-indent.
;; comment-indent *also* checks if comment-insert-comment-function is non-nil.
;; - if so, it calls it.
;; - if not, it *also* checks whether the line is empty.
;;   - if so, it inserts block-comment-start and block-comment end.
;;   - if not, it inserts comment-start and comment-end.
;; Thus, to avoid infinite loops and get block comments exactly on empty lines, we define our value of comment-insert-comment-function as follows:
(defun narya-insert-comment ()
	;; If the line is empty,
  (if (save-excursion (beginning-of-line) (looking-at "\\s-*$"))
			;; Directly insert block-comment-start and block-comment-end, like comment-dwim does but using the block ones.
      (progn
				(indent-according-to-mode)
        (insert (comment-padright block-comment-start nil))
          (save-excursion
            (insert (comment-padleft block-comment-end nil))
            (indent-according-to-mode)))
		;; Otherwise, call comment-indent, but dynamically unbinding comment-insert-comment-function so that we don't get called again in an infinite loop.
		(let ((comment-insert-comment-function nil))
			(comment-indent))))

;; Make commenting out regions use block comments.
(defun narya-comment-region (beg end &optional arg)
	(let ((comment-start block-comment-start)
				(comment-end block-comment-end)
				(comment-continue "")
				(comment-style 'extra-line))
		(comment-region-default beg end arg)))

(defun narya-mode-extra-config ()
	(set (make-local-variable 'block-comment-start) "{` ")
	(set (make-local-variable 'block-comment-end) " `}")
	(set (make-local-variable 'comment-insert-comment-function) 'narya-insert-comment)
	(set (make-local-variable 'comment-region-function) 'narya-comment-region))

(add-hook 'narya-mode-hook 'narya-mode-extra-config)

(provide 'narya)

;;; narya.el ends here
