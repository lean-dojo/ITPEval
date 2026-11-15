;; Statement-only formalization of Babel-formal artifact zero_le_one_elem:
;; identity/zero matrices and their pointwise preorder/equality laws over
;; arbitrary index and element carriers. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defstub zloe-index-p (index-type x) t)
(defstub zloe-element-p (element-type x) t)

(defstub zloe-dec-eq (index-type x y) t)
(defstub zloe-zero (element-type) t)
(defstub zloe-one (element-type) t)
(defstub zloe-le (element-type x y) t)

;; Arbitrary source matrices are first-order codes interpreted by this stub.
(defstub zloe-base-matrix-entry
  (index-type element-type matrix-code i j)
  t)

(defun zloe-zero-matrix ()
  (list :zloe-zero-matrix))

(defun zloe-one-matrix ()
  (list :zloe-one-matrix))

(defun zloe-matrix-entry
    (index-type element-type matrix i j)
  (cond
   ((equal matrix (zloe-zero-matrix))
    (zloe-zero element-type))
   ((equal matrix (zloe-one-matrix))
    (if (zloe-dec-eq index-type i j)
        (zloe-one element-type)
      (zloe-zero element-type)))
   (t
    (zloe-base-matrix-entry
     index-type element-type matrix i j))))

(defun-sk zloe-dec-eq-boolean-p (index-type)
  (forall (i j)
    (implies
     (and
      (zloe-index-p index-type i)
      (zloe-index-p index-type j))
     (booleanp (zloe-dec-eq index-type i j)))))

(defun-sk zloe-matrix-typed-p
    (index-type element-type matrix)
  (forall (i j)
    (implies
     (and
      (zloe-index-p index-type i)
      (zloe-index-p index-type j))
     (zloe-element-p
      element-type
      (zloe-matrix-entry
       index-type element-type matrix i j)))))

(defun-sk zloe-preorder-refl-p (element-type)
  (forall (x)
    (implies
     (zloe-element-p element-type x)
     (zloe-le element-type x x))))

(defun-sk zloe-preorder-trans-p (element-type)
  (forall (x y z)
    (implies
     (and
      (zloe-element-p element-type x)
      (zloe-element-p element-type y)
      (zloe-element-p element-type z)
      (zloe-le element-type x y)
      (zloe-le element-type y z))
     (zloe-le element-type x z))))

(defun-sk zloe-order-antisymmetric-p (element-type)
  (forall (x y)
    (implies
     (and
      (zloe-element-p element-type x)
      (zloe-element-p element-type y)
      (zloe-le element-type x y)
      (zloe-le element-type y x))
     (equal x y))))

(defun zloe-context-p (index-type element-type)
  (and
   (zloe-element-p element-type (zloe-zero element-type))
   (zloe-element-p element-type (zloe-one element-type))
   (zloe-dec-eq-boolean-p index-type)
   (zloe-preorder-refl-p element-type)
   (zloe-preorder-trans-p element-type)
   (zloe-le
    element-type
    (zloe-zero element-type)
    (zloe-one element-type))
   (zloe-le
    element-type
    (zloe-zero element-type)
    (zloe-zero element-type))))

(defun-sk zloe-matrix-le-p
    (index-type element-type matrix-a matrix-b)
  (forall (i j)
    (implies
     (and
      (zloe-index-p index-type i)
      (zloe-index-p index-type j))
     (zloe-le
      element-type
      (zloe-matrix-entry
       index-type element-type matrix-a i j)
      (zloe-matrix-entry
       index-type element-type matrix-b i j)))))

(defun-sk zloe-matrix-eq-p
    (index-type element-type matrix-a matrix-b)
  (forall (i j)
    (implies
     (and
      (zloe-index-p index-type i)
      (zloe-index-p index-type j))
     (equal
      (zloe-matrix-entry
       index-type element-type matrix-a i j)
      (zloe-matrix-entry
       index-type element-type matrix-b i j)))))

(defun-sk zloe-zero-le-one-elem-statement ()
  (forall (index-type element-type i j)
    (implies
     (and
      (zloe-context-p index-type element-type)
      (zloe-index-p index-type i)
      (zloe-index-p index-type j))
     (zloe-le
      element-type
      (zloe-zero element-type)
      (zloe-matrix-entry
       index-type
       element-type
       (zloe-one-matrix)
       i
       j)))))

(defun-sk zloe-zero-le-one-matrix-statement ()
  (forall (index-type element-type)
    (implies
     (zloe-context-p index-type element-type)
     (zloe-matrix-le-p
      index-type
      element-type
      (zloe-zero-matrix)
      (zloe-one-matrix)))))

(defun-sk zloe-matrix-le-refl-statement ()
  (forall (index-type element-type matrix-a)
    (implies
     (and
      (zloe-context-p index-type element-type)
      (zloe-matrix-typed-p
       index-type element-type matrix-a))
     (zloe-matrix-le-p
      index-type element-type matrix-a matrix-a))))

(defun-sk zloe-matrix-le-trans-statement ()
  (forall
   (index-type element-type matrix-a matrix-b matrix-c)
    (implies
     (and
      (zloe-context-p index-type element-type)
      (zloe-matrix-typed-p
       index-type element-type matrix-a)
      (zloe-matrix-typed-p
       index-type element-type matrix-b)
      (zloe-matrix-typed-p
       index-type element-type matrix-c)
      (zloe-matrix-le-p
       index-type element-type matrix-a matrix-b)
      (zloe-matrix-le-p
       index-type element-type matrix-b matrix-c))
     (zloe-matrix-le-p
      index-type element-type matrix-a matrix-c))))

(defun-sk zloe-matrix-eq-refl-statement ()
  (forall (index-type element-type matrix-a)
    (implies
     (and
      (zloe-context-p index-type element-type)
      (zloe-matrix-typed-p
       index-type element-type matrix-a))
     (zloe-matrix-eq-p
      index-type element-type matrix-a matrix-a))))

(defun-sk zloe-matrix-eq-sym-statement ()
  (forall (index-type element-type matrix-a matrix-b)
    (implies
     (and
      (zloe-context-p index-type element-type)
      (zloe-matrix-typed-p
       index-type element-type matrix-a)
      (zloe-matrix-typed-p
       index-type element-type matrix-b)
      (zloe-matrix-eq-p
       index-type element-type matrix-a matrix-b))
     (zloe-matrix-eq-p
      index-type element-type matrix-b matrix-a))))

(defun-sk zloe-matrix-eq-trans-statement ()
  (forall
   (index-type element-type matrix-a matrix-b matrix-c)
    (implies
     (and
      (zloe-context-p index-type element-type)
      (zloe-matrix-typed-p
       index-type element-type matrix-a)
      (zloe-matrix-typed-p
       index-type element-type matrix-b)
      (zloe-matrix-typed-p
       index-type element-type matrix-c)
      (zloe-matrix-eq-p
       index-type element-type matrix-a matrix-b)
      (zloe-matrix-eq-p
       index-type element-type matrix-b matrix-c))
     (zloe-matrix-eq-p
      index-type element-type matrix-a matrix-c))))

(defun-sk zloe-matrix-eq-le-statement ()
  (forall (index-type element-type matrix-a matrix-b)
    (implies
     (and
      (zloe-context-p index-type element-type)
      (zloe-matrix-typed-p
       index-type element-type matrix-a)
      (zloe-matrix-typed-p
       index-type element-type matrix-b)
      (zloe-matrix-eq-p
       index-type element-type matrix-a matrix-b))
     (and
      (zloe-matrix-le-p
       index-type element-type matrix-a matrix-b)
      (zloe-matrix-le-p
       index-type element-type matrix-b matrix-a)))))

(defun-sk zloe-matrix-le-antisymm-statement ()
  (forall (index-type element-type matrix-a matrix-b)
    (implies
     (and
      (zloe-context-p index-type element-type)
      (zloe-order-antisymmetric-p element-type)
      (zloe-matrix-typed-p
       index-type element-type matrix-a)
      (zloe-matrix-typed-p
       index-type element-type matrix-b)
      (zloe-matrix-le-p
       index-type element-type matrix-a matrix-b)
      (zloe-matrix-le-p
       index-type element-type matrix-b matrix-a))
     (zloe-matrix-eq-p
      index-type element-type matrix-a matrix-b))))

(defun zero-le-one-elem-statement ()
  (and
   (zloe-zero-le-one-elem-statement)
   (zloe-zero-le-one-matrix-statement)
   (zloe-matrix-le-refl-statement)
   (zloe-matrix-le-trans-statement)
   (zloe-matrix-eq-refl-statement)
   (zloe-matrix-eq-sym-statement)
   (zloe-matrix-eq-trans-statement)
   (zloe-matrix-eq-le-statement)
   (zloe-matrix-le-antisymm-statement)))

(value-triple :itpeval-statement-checked)
:q
