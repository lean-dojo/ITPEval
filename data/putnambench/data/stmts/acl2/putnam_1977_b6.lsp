;; Statement-only formalization of PutnamBench corpus artifact putnam_1977_b6:
;; a finite subgroup satisfying (x*a)^3 = 1 has at most 3*h^2 distinct
;; nonempty alternating products x_1*a*...*x_n*a. This file contains no proof.

(in-package "ACL2")

;; CARRIER, OP, and INV are ACL2 function objects. Generated predicate
;; lambdas return T outside CARRIER, so FN-EQUAL against a constant-T lambda
;; expresses each universally quantified group law on the represented type.

(defun putnam-1977-b6-quoted (object)
  (list 'quote object))

(defun putnam-1977-b6-apply1-term (function argument)
  (list 'apply$
        (putnam-1977-b6-quoted function)
        (list 'cons argument nil)))

(defun putnam-1977-b6-apply2-term (function left right)
  (list 'apply$
        (putnam-1977-b6-quoted function)
        (list 'cons left
              (list 'cons right nil))))

(defun putnam-1977-b6-carrier-term (carrier element)
  (putnam-1977-b6-apply1-term carrier element))

(defun putnam-1977-b6-operation-term (op left right)
  (putnam-1977-b6-apply2-term op left right))

(defun putnam-1977-b6-inverse-term (inv element)
  (putnam-1977-b6-apply1-term inv element))

(defun putnam-1977-b6-all-in-carrier-term
    (carrier variables)
  (if (endp variables)
      (putnam-1977-b6-quoted t)
    (list 'if
          (putnam-1977-b6-carrier-term
           carrier (car variables))
          (putnam-1977-b6-all-in-carrier-term
           carrier (cdr variables))
          (putnam-1977-b6-quoted nil))))

(defun putnam-1977-b6-restricted-predicate-term
    (carrier variables proposition)
  (list 'if
        (putnam-1977-b6-all-in-carrier-term
         carrier variables)
        proposition
        (putnam-1977-b6-quoted t)))

(defun putnam-1977-b6-and-term (left right)
  (list 'if left right (putnam-1977-b6-quoted nil)))

(defun putnam-1977-b6-true-function (formals)
  (list 'lambda formals (putnam-1977-b6-quoted t)))

(defun putnam-1977-b6-operation-closure-function (carrier op)
  (let ((op-xy
         (putnam-1977-b6-operation-term op 'x 'y)))
    (list
     'lambda
     '(x y)
     (putnam-1977-b6-restricted-predicate-term
      carrier
      '(x y)
      (putnam-1977-b6-carrier-term carrier op-xy)))))

(defun putnam-1977-b6-inverse-closure-function (carrier inv)
  (list
   'lambda
   '(x)
   (putnam-1977-b6-restricted-predicate-term
    carrier
    '(x)
    (putnam-1977-b6-carrier-term
     carrier
     (putnam-1977-b6-inverse-term inv 'x)))))

(defun putnam-1977-b6-associative-function (carrier op)
  (let* ((op-xy
          (putnam-1977-b6-operation-term op 'x 'y))
         (op-yz
          (putnam-1977-b6-operation-term op 'y 'z)))
    (list
     'lambda
     '(x y z)
     (putnam-1977-b6-restricted-predicate-term
      carrier
      '(x y z)
      (list
       'equal
       (putnam-1977-b6-operation-term op op-xy 'z)
       (putnam-1977-b6-operation-term op 'x op-yz))))))

(defun putnam-1977-b6-identity-function (carrier op one)
  (let ((left
         (list
          'equal
          (putnam-1977-b6-operation-term
           op (putnam-1977-b6-quoted one) 'x)
          'x))
        (right
         (list
          'equal
          (putnam-1977-b6-operation-term
           op 'x (putnam-1977-b6-quoted one))
          'x)))
    (list
     'lambda
     '(x)
     (putnam-1977-b6-restricted-predicate-term
      carrier
      '(x)
      (putnam-1977-b6-and-term left right)))))

(defun putnam-1977-b6-inverse-law-function
    (carrier op inv one)
  (let* ((inv-x
          (putnam-1977-b6-inverse-term inv 'x))
         (left
          (list
           'equal
           (putnam-1977-b6-operation-term op inv-x 'x)
           (putnam-1977-b6-quoted one)))
         (right
          (list
           'equal
           (putnam-1977-b6-operation-term op 'x inv-x)
           (putnam-1977-b6-quoted one))))
    (list
     'lambda
     '(x)
     (putnam-1977-b6-restricted-predicate-term
      carrier
      '(x)
      (putnam-1977-b6-and-term left right)))))

(defun putnam-1977-b6-member-p (carrier element)
  (apply$ carrier (list element)))

(defun putnam-1977-b6-multiply (op left right)
  (apply$ op (list left right)))

(defun putnam-1977-b6-inverse (inv element)
  (apply$ inv (list element)))

(defun putnam-1977-b6-power (op base exponent one)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (putnam-1977-b6-multiply
     op
     base
     (putnam-1977-b6-power
      op base (- exponent 1) one))))

(defun putnam-1977-b6-group-p (carrier op inv one)
  (and
   (tamep-functionp carrier)
   (tamep-functionp op)
   (tamep-functionp inv)
   (putnam-1977-b6-member-p carrier one)
   (fn-equal
    (putnam-1977-b6-operation-closure-function carrier op)
    (putnam-1977-b6-true-function '(x y)))
   (fn-equal
    (putnam-1977-b6-inverse-closure-function carrier inv)
    (putnam-1977-b6-true-function '(x)))
   (fn-equal
    (putnam-1977-b6-associative-function carrier op)
    (putnam-1977-b6-true-function '(x y z)))
   (fn-equal
    (putnam-1977-b6-identity-function carrier op one)
    (putnam-1977-b6-true-function '(x)))
   (fn-equal
    (putnam-1977-b6-inverse-law-function carrier op inv one)
    (putnam-1977-b6-true-function '(x)))))

(defun putnam-1977-b6-subset-of-carrier-p
    (elements carrier)
  (if (endp elements)
      t
    (and
     (putnam-1977-b6-member-p carrier (car elements))
     (putnam-1977-b6-subset-of-carrier-p
      (cdr elements) carrier))))

(defun putnam-1977-b6-subgroup-product-row-p
    (x elements subgroup op)
  (if (endp elements)
      t
    (and
     (member-equal
      (putnam-1977-b6-multiply op x (car elements))
      subgroup)
     (putnam-1977-b6-subgroup-product-row-p
      x (cdr elements) subgroup op))))

(defun putnam-1977-b6-subgroup-product-closed-p
    (elements subgroup op)
  (if (endp elements)
      t
    (and
     (putnam-1977-b6-subgroup-product-row-p
      (car elements) subgroup subgroup op)
     (putnam-1977-b6-subgroup-product-closed-p
      (cdr elements) subgroup op))))

(defun putnam-1977-b6-subgroup-inverse-closed-p
    (elements subgroup inv)
  (if (endp elements)
      t
    (and
     (member-equal
      (putnam-1977-b6-inverse inv (car elements))
      subgroup)
     (putnam-1977-b6-subgroup-inverse-closed-p
      (cdr elements) subgroup inv))))

(defun putnam-1977-b6-subgroup-p
    (subgroup carrier op inv one)
  (and
   (true-listp subgroup)
   (no-duplicatesp-equal subgroup)
   (putnam-1977-b6-subset-of-carrier-p subgroup carrier)
   (member-equal one subgroup)
   (putnam-1977-b6-subgroup-product-closed-p
    subgroup subgroup op)
   (putnam-1977-b6-subgroup-inverse-closed-p
    subgroup subgroup inv)))

(defun putnam-1977-b6-cube-hypothesis-p
    (elements op a one)
  (if (endp elements)
      t
    (and
     (equal
      (putnam-1977-b6-power
       op
       (putnam-1977-b6-multiply op (car elements) a)
       3
       one)
      one)
     (putnam-1977-b6-cube-hypothesis-p
      (cdr elements) op a one))))

(defun putnam-1977-b6-word-elements-p (word subgroup)
  (if (endp word)
      t
    (and
     (member-equal (car word) subgroup)
     (putnam-1977-b6-word-elements-p
      (cdr word) subgroup))))

(defun putnam-1977-b6-product-word-p (word subgroup)
  (and
   (true-listp word)
   (consp word)
   (putnam-1977-b6-word-elements-p word subgroup)))

(defun putnam-1977-b6-product-words-p
    (words subgroup)
  (if (endp words)
      t
    (and
     (putnam-1977-b6-product-word-p
      (car words) subgroup)
     (putnam-1977-b6-product-words-p
      (cdr words) subgroup))))

(defun putnam-1977-b6-product-value
    (word op a one)
  (if (endp word)
      one
    (putnam-1977-b6-multiply
     op
     (putnam-1977-b6-multiply op (car word) a)
     (putnam-1977-b6-product-value
      (cdr word) op a one))))

(defun putnam-1977-b6-product-values
    (words op a one)
  (if (endp words)
      nil
    (cons
     (putnam-1977-b6-product-value
      (car words) op a one)
     (putnam-1977-b6-product-values
      (cdr words) op a one))))

;; P is the image of nonempty H-words under PRODUCT-VALUE. For N = 3*h^2,
;; "P is finite and |P| <= N" is equivalent to saying that every list of
;; N+1 such words has two equal image values.

(defun-sk putnam-1977-b6-cardinality-bound-p
    (subgroup op a one h)
  (forall (words)
    (implies
     (and
      (true-listp words)
      (putnam-1977-b6-product-words-p words subgroup)
      (equal
       (len words)
       (+ 1 (* 3 (expt h 2)))))
     (not
      (no-duplicatesp-equal
       (putnam-1977-b6-product-values
        words op a one))))))

(defun putnambench-putnam-1977-b6-statement
    (carrier op inv one subgroup h a)
  (implies
   (and
    (putnam-1977-b6-group-p carrier op inv one)
    (putnam-1977-b6-subgroup-p
     subgroup carrier op inv one)
    (natp h)
    (equal h (len subgroup))
    (putnam-1977-b6-member-p carrier a)
    (putnam-1977-b6-cube-hypothesis-p
     subgroup op a one))
   (putnam-1977-b6-cardinality-bound-p
    subgroup op a one h)))

(value-triple :itpeval-statement-checked)
:q
