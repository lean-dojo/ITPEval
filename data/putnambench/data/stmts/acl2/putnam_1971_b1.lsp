;; Statement-only formalization of PutnamBench corpus artifact putnam_1971_b1:
;; an idempotent binary operation satisfying the cyclic three-variable law is
;; associative and commutative. This file contains no proof.

(in-package "ACL2")

;; CARRIER and OP are ACL2 function objects.  The generated predicate lambdas
;; return T outside CARRIER, so FN-EQUAL with the matching constant-T lambda
;; expresses universal quantification over exactly the represented type.

(defun putnam-1971-b1-quoted (object)
  (list 'quote object))

(defun putnam-1971-b1-apply1-term (function argument)
  (list 'apply$
        (putnam-1971-b1-quoted function)
        (list 'cons argument nil)))

(defun putnam-1971-b1-apply2-term (function left right)
  (list 'apply$
        (putnam-1971-b1-quoted function)
        (list 'cons left
              (list 'cons right nil))))

(defun putnam-1971-b1-carrier-term (carrier element)
  (putnam-1971-b1-apply1-term carrier element))

(defun putnam-1971-b1-operation-term (op left right)
  (putnam-1971-b1-apply2-term op left right))

(defun putnam-1971-b1-all-in-carrier-term
    (carrier variables)
  (if (endp variables)
      t
    (list 'if
          (putnam-1971-b1-carrier-term
           carrier (car variables))
          (putnam-1971-b1-all-in-carrier-term
           carrier (cdr variables))
          nil)))

(defun putnam-1971-b1-restricted-predicate-term
    (carrier variables proposition)
  (list 'if
        (putnam-1971-b1-all-in-carrier-term
         carrier variables)
        proposition
        t))

(defun putnam-1971-b1-true-function (formals)
  (list 'lambda formals t))

(defun putnam-1971-b1-closure-function (carrier op)
  (let ((op-xy
         (putnam-1971-b1-operation-term op 'x 'y)))
    (list
     'lambda
     '(x y)
     (putnam-1971-b1-restricted-predicate-term
      carrier
      '(x y)
      (putnam-1971-b1-carrier-term carrier op-xy)))))

(defun putnam-1971-b1-idempotent-function (carrier op)
  (list
   'lambda
   '(x)
   (putnam-1971-b1-restricted-predicate-term
    carrier
    '(x)
    (list
     'equal
     (putnam-1971-b1-operation-term op 'x 'x)
     'x))))

(defun putnam-1971-b1-cyclic-function (carrier op)
  (let* ((op-xy
          (putnam-1971-b1-operation-term op 'x 'y))
         (op-yz
          (putnam-1971-b1-operation-term op 'y 'z)))
    (list
     'lambda
     '(x y z)
     (putnam-1971-b1-restricted-predicate-term
      carrier
      '(x y z)
      (list
       'equal
       (putnam-1971-b1-operation-term op op-xy 'z)
       (putnam-1971-b1-operation-term op op-yz 'x))))))

(defun putnam-1971-b1-associative-function (carrier op)
  (let* ((op-xy
          (putnam-1971-b1-operation-term op 'x 'y))
         (op-yz
          (putnam-1971-b1-operation-term op 'y 'z)))
    (list
     'lambda
     '(x y z)
     (putnam-1971-b1-restricted-predicate-term
      carrier
      '(x y z)
      (list
       'equal
       (putnam-1971-b1-operation-term op op-xy 'z)
       (putnam-1971-b1-operation-term op 'x op-yz))))))

(defun putnam-1971-b1-commutative-function (carrier op)
  (list
   'lambda
   '(x y)
   (putnam-1971-b1-restricted-predicate-term
    carrier
    '(x y)
    (list
     'equal
     (putnam-1971-b1-operation-term op 'x 'y)
     (putnam-1971-b1-operation-term op 'y 'x)))))

(defun putnambench-putnam-1971-b1-statement (carrier op)
  (implies
   (and
    (tamep-functionp carrier)
    (tamep-functionp op)
    (fn-equal
     (putnam-1971-b1-closure-function carrier op)
     (putnam-1971-b1-true-function '(x y)))
    (fn-equal
     (putnam-1971-b1-idempotent-function carrier op)
     (putnam-1971-b1-true-function '(x)))
    (fn-equal
     (putnam-1971-b1-cyclic-function carrier op)
     (putnam-1971-b1-true-function '(x y z))))
   (and
    (fn-equal
     (putnam-1971-b1-associative-function carrier op)
     (putnam-1971-b1-true-function '(x y z)))
    (fn-equal
     (putnam-1971-b1-commutative-function carrier op)
     (putnam-1971-b1-true-function '(x y))))))

(value-triple :itpeval-statement-checked)
:q
