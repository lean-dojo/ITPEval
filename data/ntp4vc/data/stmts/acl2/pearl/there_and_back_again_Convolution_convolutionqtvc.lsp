;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/there_and_back_again_Convolution_convolutionqtvc: the symbolic
;; convolution verification condition for equal-length lists, relating a
;; consumed prefix, its reversal, the paired output, and the remaining suffix.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent the source's arbitrary inhabited
;; element type.

(defstub tba-convolution-element-p (value) t)
(defstub tba-convolution-default-element () t)

(defun tba-convolution-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (tba-convolution-element-p (car xs))
       (tba-convolution-list-p (cdr xs)))
    (equal xs nil)))

;; A source pair (a,b) is represented by the injective ACL2 cons pair
;; (cons a b).

(defun tba-convolution-pair-p (pair)
  (and
   (consp pair)
   (tba-convolution-element-p (car pair))
   (tba-convolution-element-p (cdr pair))))

(defun tba-convolution-pair-list-p (pairs)
  (declare (xargs :measure (acl2-count pairs)))
  (if (consp pairs)
      (and
       (tba-convolution-pair-p (car pairs))
       (tba-convolution-pair-list-p (cdr pairs)))
    (equal pairs nil)))

;; This is the source combine/zip operation, stopping when either input list
;; is empty.

(defun tba-convolution-zip (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (and (consp left)
           (consp right))
      (cons
       (cons (car left) (car right))
       (tba-convolution-zip (cdr left) (cdr right)))
    nil))

;; The prefix witness remains existentially quantified inside the premise:
;; Y is PREFIX ++ SUFFIX, PREFIX has the length of X, and PAIRS is the zip of
;; X with the reverse of PREFIX.

(defun-sk tba-convolution-prefix-witness-p (x y suffix pairs)
  (exists (prefix)
    (and
     (tba-convolution-list-p prefix)
     (equal y (append prefix suffix))
     (equal (len prefix) (len x))
     (equal
      pairs
      (tba-convolution-zip x (reverse prefix))))))

;; PAIRS and SUFFIX retain their universal scope. The guards are exactly the
;; target rendering of their source list types.

(defun-sk tba-convolution-all-results-p (x y)
  (forall (pairs suffix)
    (implies
     (and
      (tba-convolution-pair-list-p pairs)
      (tba-convolution-list-p suffix))
     (implies
      (tba-convolution-prefix-witness-p x y suffix pairs)
      (equal
       pairs
       (tba-convolution-zip x (reverse y)))))))

(defun
  ntp4vc-pearl-there-and-back-again-convolution-convolutionqtvc-statement
  (x y)
  (implies
   (and
    (tba-convolution-element-p
     (tba-convolution-default-element))
    (tba-convolution-list-p x)
    (tba-convolution-list-p y)
    (equal (len x) (len y)))
   (and
    (<= (len x) (len y))
    (tba-convolution-all-results-p x y))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
