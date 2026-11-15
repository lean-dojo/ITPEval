;; Statement-only formalization of hundred-theorems artifact
;; hundred-theorems__acl2__074, "The Principle of Mathematical Induction":
;; for every predicate on the natural numbers, truth at zero and preservation
;; by successor imply truth at every natural number. This file contains no
;; proof.

(in-package "ACL2")

;; Under universal closure, VALUES records P(0), ..., P(n). This is not a
;; bounded-predicate approximation: restricting any total P gives such a
;; trace, while every Boolean trace extends to a total P by keeping its final
;; value constant after n. Trace length is unbounded, so every natural n
;; occurs. The adjacent implications then become the global successor
;; hypothesis. Thus the trace statement and the usual quantification over P
;; and n imply each other.
(defun ht074-boolean-trace-p (values)
  (if (atom values)
      (equal values nil)
    (and (or (equal (car values) t)
             (equal (car values) nil))
         (ht074-boolean-trace-p (cdr values)))))

(defun ht074-successor-step-chain-p (values)
  (if (or (atom values)
          (atom (cdr values)))
      t
    (and (implies (equal (car values) t)
                  (equal (cadr values) t))
         (ht074-successor-step-chain-p (cdr values)))))

(defun hundred-theorems-074-principle-of-mathematical-induction-statement
    (values n)
  (implies
   (and (natp n)
        (ht074-boolean-trace-p values)
        (equal (len values) (+ n 1))
        (equal (car values) t)
        (ht074-successor-step-chain-p values))
   (equal (nth n values) t)))

(value-triple :itpeval-statement-checked)
:q
