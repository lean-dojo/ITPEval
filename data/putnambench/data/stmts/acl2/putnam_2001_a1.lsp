;; Statement-only formalization of PutnamBench corpus artifact putnam_2001_a1:
;; an involutive law for an arbitrary binary operation implies its reversed
;; involutive law. This file contains no proof.

(in-package "ACL2")

;; CARRIER and OP are ACL2 function objects. The generated predicate lambdas
;; return T outside CARRIER, so FN-EQUAL against a constant-T lambda expresses
;; universal quantification over exactly the represented type. Closure is the
;; explicit ACL2 counterpart of the source's typed binary operation.

(defun putnam-2001-a1-quoted (object)
  (list 'quote object))

(defun putnam-2001-a1-apply1-term (function argument)
  (list 'apply$
        (putnam-2001-a1-quoted function)
        (list 'cons argument nil)))

(defun putnam-2001-a1-apply2-term (function left right)
  (list 'apply$
        (putnam-2001-a1-quoted function)
        (list 'cons left
              (list 'cons right nil))))

(defun putnam-2001-a1-carrier-term (carrier element)
  (putnam-2001-a1-apply1-term carrier element))

(defun putnam-2001-a1-operation-term (op left right)
  (putnam-2001-a1-apply2-term op left right))

(defun putnam-2001-a1-all-in-carrier-term
    (carrier variables)
  (if (endp variables)
      (putnam-2001-a1-quoted t)
    (list 'if
          (putnam-2001-a1-carrier-term
           carrier (car variables))
          (putnam-2001-a1-all-in-carrier-term
           carrier (cdr variables))
          (putnam-2001-a1-quoted nil))))

(defun putnam-2001-a1-restricted-predicate-term
    (carrier variables proposition)
  (list 'if
        (putnam-2001-a1-all-in-carrier-term
         carrier variables)
        proposition
        (putnam-2001-a1-quoted t)))

(defun putnam-2001-a1-true-function (formals)
  (list 'lambda formals (putnam-2001-a1-quoted t)))

(defun putnam-2001-a1-closure-function (carrier op)
  (let ((op-ab
         (putnam-2001-a1-operation-term op 'a 'b)))
    (list
     'lambda
     '(a b)
     (putnam-2001-a1-restricted-predicate-term
      carrier
      '(a b)
      (putnam-2001-a1-carrier-term carrier op-ab)))))

(defun putnam-2001-a1-hypothesis-function (carrier op)
  (let ((op-ab
         (putnam-2001-a1-operation-term op 'a 'b)))
    (list
     'lambda
     '(a b)
     (putnam-2001-a1-restricted-predicate-term
      carrier
      '(a b)
      (list
       'equal
       (putnam-2001-a1-operation-term op op-ab 'a)
       'b)))))

(defun putnam-2001-a1-conclusion-function (carrier op)
  (let ((op-ba
         (putnam-2001-a1-operation-term op 'b 'a)))
    (list
     'lambda
     '(a b)
     (putnam-2001-a1-restricted-predicate-term
      carrier
      '(a b)
      (list
       'equal
       (putnam-2001-a1-operation-term op 'a op-ba)
       'b)))))

(defun putnambench-putnam-2001-a1-statement (carrier op)
  (implies
   (and
    (tamep-functionp carrier)
    (tamep-functionp op)
    (fn-equal
     (putnam-2001-a1-closure-function carrier op)
     (putnam-2001-a1-true-function '(a b)))
    (fn-equal
     (putnam-2001-a1-hypothesis-function carrier op)
     (putnam-2001-a1-true-function '(a b))))
   (fn-equal
    (putnam-2001-a1-conclusion-function carrier op)
    (putnam-2001-a1-true-function '(a b)))))

(value-triple :itpeval-statement-checked)
:q
