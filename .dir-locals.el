((nil . ((eval . (let ((default-directory (locate-dominating-file
						buffer-file-name ".dir-locals.el")))
			(make-local-variable 'compile-command)
			(setq compile-command (format "make -k --directory=\"%s\""
						      (expand-file-name ".")))))))
 (coq-mode . ((eval . (let ((default-directory (locate-dominating-file
						buffer-file-name ".dir-locals.el")))
			(make-local-variable 'coq-load-path)
			(setq coq-load-path `((,(expand-file-name ".") "ADTSynthesis"))))))))
