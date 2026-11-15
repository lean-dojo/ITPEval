;; Statement-only formalization of PutnamBench corpus artifact putnam_2003_b2:
;; the final value obtained by repeatedly averaging adjacent terms of
;; 1, 1/2, ..., 1/n is strictly less than 2/n. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; SEQUENCE is a total tame binary function object on natural indices, with
;; rational codomain enforced below by FN-EQUAL. The source hypotheses and
;; conclusion inspect only the finite triangle
;;
;;   0 <= k < n,  1 <= j <= n-k.
;;
;; Every source sequence restricts on this triangle to values represented by
;; a tame nested-IF function (with rational default zero), and every qualifying
;; target function gives a source sequence. Thus restricting the representing
;; function object to tame functions is bidirectionally equivalent for this
;; proposition and does not replace the sequence by a finite table.

(defun putnam-2003-b2-quoted (object)
  (list 'quote object))

(defun putnam-2003-b2-term-list (terms)
  (if (consp terms)
      (list 'cons
            (car terms)
            (putnam-2003-b2-term-list (cdr terms)))
    nil))

(defun putnam-2003-b2-apply-term (function arguments)
  (list 'apply$
        (putnam-2003-b2-quoted function)
        (putnam-2003-b2-term-list arguments)))

(defun putnam-2003-b2-and-terms (terms)
  (if (consp terms)
      (list 'if
            (car terms)
            (putnam-2003-b2-and-terms (cdr terms))
            (putnam-2003-b2-quoted nil))
    (putnam-2003-b2-quoted t)))

(defun putnam-2003-b2-implies-term (hypothesis conclusion)
  (list 'if
        hypothesis
        conclusion
        (putnam-2003-b2-quoted t)))

(defun putnam-2003-b2-true-function (formals)
  (list 'lambda formals (putnam-2003-b2-quoted t)))

(defun putnam-2003-b2-codomain-function (sequence)
  (let ((value
         (putnam-2003-b2-apply-term
          sequence '(k j))))
    (list
     'lambda
     '(k j)
     (putnam-2003-b2-implies-term
      (putnam-2003-b2-and-terms
       (list (list 'natp 'k)
             (list 'natp 'j)))
      (list 'rationalp value)))))

(defun putnam-2003-b2-rational-sequence-p (sequence)
  (let ((codomain
         (putnam-2003-b2-codomain-function sequence))
        (true-on-two
         (putnam-2003-b2-true-function '(k j))))
    (and
     (tamep-functionp sequence)
     (tamep-functionp codomain)
     (tamep-functionp true-on-two)
     (fn-equal codomain true-on-two))))

(defun putnam-2003-b2-sequence-value (sequence k j)
  (apply$ sequence (list k j)))

(defun putnam-2003-b2-initial-p (sequence j)
  (declare (xargs :measure (nfix j)))
  (if (zp j)
      t
    (and
     (equal
      (putnam-2003-b2-sequence-value sequence 0 j)
      (/ 1 j))
     (putnam-2003-b2-initial-p sequence (- j 1)))))

(defun putnam-2003-b2-averaging-row-p
    (sequence k j)
  (declare (xargs :measure (nfix j)))
  (if (zp j)
      t
    (and
     (equal
      (putnam-2003-b2-sequence-value sequence k j)
      (/
       (+
        (putnam-2003-b2-sequence-value
         sequence (- k 1) j)
        (putnam-2003-b2-sequence-value
         sequence (- k 1) (+ j 1)))
       2))
     (putnam-2003-b2-averaging-row-p
      sequence k (- j 1)))))

(defun putnam-2003-b2-averaging-p
    (sequence n k)
  (declare (xargs :measure (nfix k)))
  (if (zp k)
      t
    (and
     (putnam-2003-b2-averaging-row-p
      sequence k (- n k))
     (putnam-2003-b2-averaging-p
      sequence n (- k 1)))))

(defun putnambench-putnam-2003-b2-statement
    (n sequence)
  (implies
   (and
    (natp n)
    (< 0 n)
    (putnam-2003-b2-rational-sequence-p sequence)
    (putnam-2003-b2-initial-p sequence n)
    (putnam-2003-b2-averaging-p
     sequence n (- n 1)))
   (<
    (putnam-2003-b2-sequence-value
     sequence (- n 1) 1)
    (/ 2 n))))

(value-triple :itpeval-statement-checked)
:q
