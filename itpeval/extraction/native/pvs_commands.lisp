(in-package :pvs)

;; Serialize each response before advancing. Later commands can mutate the
;; native proofstate object that was returned by the preceding call.
(defun itpeval-write-state (response stream)
  (let ((status (cdr (assoc "status" response :test #'equal)))
        (failure (cdr (assoc "error" response :test #'equal)))
        (states (pvs-jsonrpc::pvs2json-response response)))
    (format stream "~a~c~a~c~a~%" status #\Tab (json:encode-json-to-string states)
            #\Tab (json:encode-json-to-string failure))))

(defun itpeval-proof-target ()
  ;; Match the reviewed formula by its native source line. A file can contain
  ;; multiple theories with formulas that use the same identifier.
  (let ((name (sb-ext:posix-getenv "ITPEVAL_TARGET"))
        (line (parse-integer (sb-ext:posix-getenv "ITPEVAL_TARGET_LINE")))
        (matches nil))
    (dolist (theory (typecheck-file (sb-ext:posix-getenv "ITPEVAL_ENTRY") t))
      (dolist (decl (all-decls theory))
        (when (and (formula-decl? decl) (id decl) (place decl)
                   (string-equal (id decl) name) (= (elt (place decl) 0) line))
          (push decl matches))))
    (unless (= (length matches) 1)
      (error "Expected one named PVS formula at source line ~a" line))
    (car matches)))

(defun itpeval-horn-atom (expression atoms)
  ;; Use native declaration identity. Equal printer output alone cannot
  ;; identify a logical atom. This fragment admits only Boolean skolems.
  (when (and (name-expr? expression) (skolem-const-decl? (declaration expression))
             (tc-eq (type expression) *boolean*))
    (let* ((decl (declaration expression))
           (number (or (gethash decl atoms)
                       (setf (gethash decl atoms) (1+ (hash-table-count atoms))))))
      (pvs-jsonrpc::obj `(("atom" . ,number) ("skolem" . ,(symbol-name (id decl))))))))

(defun itpeval-horn-premise (expression atoms label)
  (let ((antecedents nil))
    (loop while (implication? expression) do
      (let ((atom (itpeval-horn-atom (args1 expression) atoms)))
        (unless (and atom (< (length antecedents) 64))
          (return-from itpeval-horn-premise nil))
        (push atom antecedents))
      (setf expression (args2 expression)))
    (let ((head (itpeval-horn-atom expression atoms)))
      (when head
        (pvs-jsonrpc::obj `(("label" . ,label)
                            ("antecedents" . ,(coerce (nreverse antecedents) 'vector))
                            ("consequent" . ,head)))))))

(defun itpeval-write-horn (response file)
  (when (and (not (cdr (assoc "error" response :test #'equal)))
             (member (cdr (assoc "status" response :test #'equal)) '("init" "waiting") :test #'equal))
    (let* ((ps (cdr (assoc "proofstate" response :test #'equal)))
           (sequent (current-goal ps))
           (positive (pos-s-forms sequent))
           (negative (neg-s-forms sequent))
           (atoms (make-hash-table :test #'eq))
           (goal (and (= (length positive) 1)
                      (itpeval-horn-atom (formula (car positive)) atoms)))
           (reason (cond ((not goal) "expected one visible Boolean skolem as the succedent")
                         ((> (length negative) 256) "more than 256 visible antecedents")))
           (clauses nil)
           (omitted nil))
      ;; Follow the native JSON sequent's numbering and omit hidden formulas.
      (unless reason
        (loop for sform in negative for label downfrom -1 do
          (let ((premise (itpeval-horn-premise (args1 (formula sform)) atoms label)))
            (if premise (push premise clauses) (push label omitted)))))
      (with-open-file (stream file :direction :output :if-exists :error)
        (write-line (json:encode-json-to-string
                     (pvs-jsonrpc::obj `(("path" . ,(format nil "~{~a~^.~}" (path-from-top ps)))
                                         ("unsupported" . ,reason)
                                         ("conclusion" . ,goal)
                                         ("premises" . ,(coerce (nreverse clauses) 'vector))
                                         ("omitted" . ,(coerce (nreverse omitted) 'vector)))))
                    stream)))))

(defun itpeval-replay-commands ()
  (let ((target (itpeval-proof-target)))
    (with-open-file (stream (sb-ext:posix-getenv "ITPEVAL_OUTPUT") :direction :output
                            :if-exists :error)
      (with-open-file (input (sb-ext:posix-getenv "ITPEVAL_COMMANDS"))
        (let* ((commands (json:decode-json-from-string (read-line input)))
               (response (prover-init target :dont-save? t))
               (id (cdr (assoc "id" response :test #'equal))))
          (format stream "theory~c~a~%" #\Tab (id (module target)))
          (itpeval-write-state response stream)
          (loop for cmd in commands do
            (unless (member (cdr (assoc "status" response :test #'equal)) '("init" "waiting")
                            :test #'equal)
              (error "commands remain after the prover finished"))
            (setf response (prover-step id cmd))
            (itpeval-write-state response stream))
          (let ((horn (sb-ext:posix-getenv "ITPEVAL_HORN_OUTPUT")))
            (when horn (itpeval-write-horn response horn)))))
      (write-line "complete" stream))))
