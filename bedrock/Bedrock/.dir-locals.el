((coq-mode . ((eval . (let ((default-directory (locate-dominating-file
						buffer-file-name ".dir-locals.el")))
			(make-local-variable 'coq-prog-args)
			(setq coq-prog-args `("-emacs" "-R" ,(expand-file-name ".") "Bedrock" "-I" ,(expand-file-name "reification"))))))))
