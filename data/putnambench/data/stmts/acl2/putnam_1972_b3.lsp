;; Statement-only formalization of PutnamBench corpus artifact putnam_1972_b3:
;; in a group, the stated relations on A and B and an odd positive power of B
;; imply that B is the identity. This file contains no proof.

(in-package "ACL2")

;; CARRIER, OP, and INV are ACL2 function objects.  The generated predicate
;; lambdas return T outside CARRIER, so FN-EQUAL against a constant-T lambda
;; expresses each universally quantified group law on the represented type.

(defun putnam-1972-b3-quoted (object)
  (list 'quote object))

(defun putnam-1972-b3-apply1-term (function argument)
  (list 'apply$
        (putnam-1972-b3-quoted function)
        (list 'cons argument nil)))

(defun putnam-1972-b3-apply2-term (function left right)
  (list 'apply$
        (putnam-1972-b3-quoted function)
        (list 'cons left
              (list 'cons right nil))))

(defun putnam-1972-b3-carrier-term (carrier element)
  (putnam-1972-b3-apply1-term carrier element))

(defun putnam-1972-b3-operation-term (op left right)
  (putnam-1972-b3-apply2-term op left right))

(defun putnam-1972-b3-inverse-term (inv element)
  (putnam-1972-b3-apply1-term inv element))

(defun putnam-1972-b3-all-in-carrier-term
    (carrier variables)
  (if (endp variables)
      (putnam-1972-b3-quoted t)
    (list 'if
          (putnam-1972-b3-carrier-term
           carrier (car variables))
          (putnam-1972-b3-all-in-carrier-term
           carrier (cdr variables))
          (putnam-1972-b3-quoted nil))))

(defun putnam-1972-b3-restricted-predicate-term
    (carrier variables proposition)
  (list 'if
        (putnam-1972-b3-all-in-carrier-term
         carrier variables)
        proposition
        (putnam-1972-b3-quoted t)))

(defun putnam-1972-b3-and-term (left right)
  (list 'if left right (putnam-1972-b3-quoted nil)))

(defun putnam-1972-b3-true-function (formals)
  (list 'lambda formals (putnam-1972-b3-quoted t)))

(defun putnam-1972-b3-operation-closure-function (carrier op)
  (let ((op-xy
         (putnam-1972-b3-operation-term op 'x 'y)))
    (list
     'lambda
     '(x y)
     (putnam-1972-b3-restricted-predicate-term
      carrier
      '(x y)
      (putnam-1972-b3-carrier-term carrier op-xy)))))

(defun putnam-1972-b3-inverse-closure-function (carrier inv)
  (list
   'lambda
   '(x)
   (putnam-1972-b3-restricted-predicate-term
    carrier
    '(x)
    (putnam-1972-b3-carrier-term
     carrier
     (putnam-1972-b3-inverse-term inv 'x)))))

(defun putnam-1972-b3-associative-function (carrier op)
  (let* ((op-xy
          (putnam-1972-b3-operation-term op 'x 'y))
         (op-yz
          (putnam-1972-b3-operation-term op 'y 'z)))
    (list
     'lambda
     '(x y z)
     (putnam-1972-b3-restricted-predicate-term
      carrier
      '(x y z)
      (list
       'equal
       (putnam-1972-b3-operation-term op op-xy 'z)
       (putnam-1972-b3-operation-term op 'x op-yz))))))

(defun putnam-1972-b3-identity-function (carrier op one)
  (let ((left
         (list
          'equal
          (putnam-1972-b3-operation-term
           op (putnam-1972-b3-quoted one) 'x)
          'x))
        (right
         (list
          'equal
          (putnam-1972-b3-operation-term
           op 'x (putnam-1972-b3-quoted one))
          'x)))
    (list
     'lambda
     '(x)
     (putnam-1972-b3-restricted-predicate-term
      carrier
      '(x)
      (putnam-1972-b3-and-term left right)))))

(defun putnam-1972-b3-inverse-law-function
    (carrier op inv one)
  (let* ((inv-x
          (putnam-1972-b3-inverse-term inv 'x))
         (left
          (list
           'equal
           (putnam-1972-b3-operation-term op inv-x 'x)
           (putnam-1972-b3-quoted one)))
         (right
          (list
           'equal
           (putnam-1972-b3-operation-term op 'x inv-x)
           (putnam-1972-b3-quoted one))))
    (list
     'lambda
     '(x)
     (putnam-1972-b3-restricted-predicate-term
      carrier
      '(x)
      (putnam-1972-b3-and-term left right)))))

(defun putnam-1972-b3-member-p (carrier element)
  (apply$ carrier (list element)))

(defun putnam-1972-b3-multiply (op left right)
  (apply$ op (list left right)))

(defun putnam-1972-b3-power (op base exponent one)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (putnam-1972-b3-multiply
     op
     base
     (putnam-1972-b3-power op base (- exponent 1) one))))

(defun putnam-1972-b3-group-p (carrier op inv one)
  (and
   (tamep-functionp carrier)
   (tamep-functionp op)
   (tamep-functionp inv)
   (putnam-1972-b3-member-p carrier one)
   (fn-equal
    (putnam-1972-b3-operation-closure-function carrier op)
    (putnam-1972-b3-true-function '(x y)))
   (fn-equal
    (putnam-1972-b3-inverse-closure-function carrier inv)
    (putnam-1972-b3-true-function '(x)))
   (fn-equal
    (putnam-1972-b3-associative-function carrier op)
    (putnam-1972-b3-true-function '(x y z)))
   (fn-equal
    (putnam-1972-b3-identity-function carrier op one)
    (putnam-1972-b3-true-function '(x)))
   (fn-equal
    (putnam-1972-b3-inverse-law-function carrier op inv one)
    (putnam-1972-b3-true-function '(x)))))

;; A trace (ONE, B, B^2, ..., B^k) has even list length exactly when its
;; positive number k of multiplication steps is odd.  Requiring its last entry
;; to be ONE is therefore equivalent to B^(2*n-1) = ONE for some n > 0.

(defun putnam-1972-b3-trace-step-function (op b)
  (list
   'lambda
   '(tail)
   (list
    'if
    (list 'consp (list 'cdr 'tail))
    (list
     'equal
     (list 'car (list 'cdr 'tail))
     (putnam-1972-b3-operation-term
      op
      (putnam-1972-b3-quoted b)
      (list 'car 'tail)))
    (putnam-1972-b3-quoted t))))

(defun putnam-1972-b3-no-odd-power-witness-function (op b one)
  (let ((one-term
         (putnam-1972-b3-quoted one))
        (steps-hold
         (list
          'always$
          (putnam-1972-b3-quoted
           (putnam-1972-b3-trace-step-function op b))
          (list 'tails 'trace))))
    (list
     'lambda
     '(trace)
     (list
      'if
      (list 'true-listp 'trace)
      (list
       'if
       (list 'consp 'trace)
       (list
        'if
        (list 'consp (list 'cdr 'trace))
        (list
         'if
         (list 'evenp (list 'len 'trace))
         (list
          'if
          (list 'equal (list 'car 'trace) one-term)
          (list
           'if
           (list 'equal
                 (list 'car (list 'last 'trace))
                 one-term)
           (list 'if
                 steps-hold
                 (putnam-1972-b3-quoted nil)
                 (putnam-1972-b3-quoted t))
           (putnam-1972-b3-quoted t))
          (putnam-1972-b3-quoted t))
         (putnam-1972-b3-quoted t))
        (putnam-1972-b3-quoted t))
       (putnam-1972-b3-quoted t))
      (putnam-1972-b3-quoted t)))))

(defun putnam-1972-b3-odd-power-exists-p (op b one)
  (let ((witness-predicate
         (putnam-1972-b3-no-odd-power-witness-function op b one)))
    (and
     (tamep-functionp witness-predicate)
     (not
      (fn-equal
       witness-predicate
       (putnam-1972-b3-true-function '(trace)))))))

(defun putnambench-putnam-1972-b3-statement
    (carrier op inv one a b)
  (implies
   (and
    (putnam-1972-b3-group-p carrier op inv one)
    (putnam-1972-b3-member-p carrier a)
    (putnam-1972-b3-member-p carrier b)
    (equal
     (putnam-1972-b3-multiply
      op
      (putnam-1972-b3-multiply op a b)
      a)
     (putnam-1972-b3-multiply
      op
      (putnam-1972-b3-multiply
       op
       b
       (putnam-1972-b3-power op a 2 one))
      b))
    (equal
     (putnam-1972-b3-power op a 3 one)
     one)
    (putnam-1972-b3-odd-power-exists-p op b one))
   (equal b one)))

(value-triple :itpeval-statement-checked)
:q
