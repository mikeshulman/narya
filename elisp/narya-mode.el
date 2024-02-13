(defvar narya-dynamic-terms '()
  "List of dynamically identified terms for highlighting.")

(defun narya-update-dynamic-terms ()
  "Parse the buffer for user-defined constants following 'axiom|def const' and update dynamic terms."
  (save-excursion
    (goto-char (point-min))
    (let ((terms '()))
      (setq my-proof-dynamic-terms '())
      (while (re-search-forward "\\(axiom\\|def\\) \\([a-zA-Z0-9]+\\(?:_+[a-zA-Z0-9]+\\)*\\)\\s-*:" nil t)
        (let ((const-name (match-string 2)))
          (unless (member const-name terms)
            (push const-name terms))))
      ;; Remove duplicates and update the global list
      (setq narya-dynamic-terms (delete-dups terms)))))

(defun narya-apply-dynamic-highlighting ()
  "Apply dynamic highlighting for terms in `narya-dynamic-terms`."
  (font-lock-add-keywords nil `((,(regexp-opt narya-dynamic-terms 'words) . 'font-lock-function-name-face)) t))

;; Define the syntax highlighting
(defvar narya-font-lock-keywords
  `(
    ("\\<\\(axiom\\|def\\|echo\\)\\>" . 'font-lock-keyword-face)
    ("\\<\\(Type\\|Id\\|refl\\|sym\\|Gel\\|ungel\\)\\>" . 'font-lock-constant-face)
    ))
    
(defun narya-setup-syntax-table ()
  ;; Line comments use a backquote `, extending to the end of the line
  ;; Block comments, starting with {` and ending with `}, support nesting.
  (modify-syntax-entry ?\` "< 23b" (syntax-table)) 
  (modify-syntax-entry ?\n "> b" (syntax-table)) 
  (modify-syntax-entry ?\{ "(}1nb" (syntax-table))
  (modify-syntax-entry ?\} "){4nb" (syntax-table))
)

;; Define the mode
(define-derived-mode narya-mode fundamental-mode "Narya"
  "A mode for editing my language files."
  (setq font-lock-defaults '(narya-font-lock-keywords))
  ;; Apply dynamic highlighting after changes
  (add-hook 'after-change-functions (lambda (start end old-len)
                                      (narya-update-dynamic-terms)
                                      (narya-apply-dynamic-highlighting))
            nil t)
  ;; Initialize dynamic highlighting
  (narya-update-dynamic-terms)
  (narya-apply-dynamic-highlighting)
  (narya-setup-syntax-table))

(provide 'narya)

;; Automatically use narya-mode for .ny files
(add-to-list 'auto-mode-alist '("\\.ny\\'" . narya-mode))
