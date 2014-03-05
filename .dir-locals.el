((coq-mode . ((eval . (let ((default-directory (locate-dominating-file
						buffer-file-name ".dir-locals.el")))
			(make-local-variable 'coq-load-path)
			(setq coq-load-path `((,(expand-file-name ".") "ADTSynthesis"))))))))
