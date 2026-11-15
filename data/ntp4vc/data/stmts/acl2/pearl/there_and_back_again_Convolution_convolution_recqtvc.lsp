;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/there_and_back_again_Convolution_convolution_recqtvc: the recursive
;; symbolic-convolution verification condition relating a consumed prefix,
;; its reversal, the paired result, and the unconsumed suffix. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; These conservative interfaces represent the source's arbitrary inhabited
;; element type. Lists over that carrier and lists of ordered pairs retain
;; their source typing explicitly.

(defstub tba-conv-element-p (value) t)
(defstub tba-conv-default-element () t)

(defun tba-conv-list-p (xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (tba-conv-element-p (car xs))
       (tba-conv-list-p (cdr xs)))
    (equal xs nil)))

;; A source pair (a,b) is represented by the injective ACL2 cons pair
;; (cons a b), not by a finite tag or table.

(defun tba-conv-pair-p (pair)
  (and
   (consp pair)
   (tba-conv-element-p (car pair))
   (tba-conv-element-p (cdr pair))))

(defun tba-conv-pair-list-p (pairs)
  (declare (xargs :measure (acl2-count pairs)))
  (if (consp pairs)
      (and
       (tba-conv-pair-p (car pairs))
       (tba-conv-pair-list-p (cdr pairs)))
    (equal pairs nil)))

;; This is the source list combine/zip operation. It stops when either input
;; is empty, exactly as the Why3, Lean, Rocq, and Isabelle list operations do.

(defun tba-conv-zip (left right)
  (declare (xargs :measure (acl2-count left)))
  (if (and (consp left)
           (consp right))
      (cons
       (cons (car left) (car right))
       (tba-conv-zip (cdr left) (cdr right)))
    nil))

;; The existential witness remains internal. This predicate is precisely the
;; postcondition relation: Y splits into Y0 and SUFFIX, Y0 has the length of
;; XS, and PAIRS zips XS with the reversal of Y0.

(defun-sk tba-conv-prefix-relation-p (xs y suffix pairs)
  (exists (y0)
    (and
     (tba-conv-list-p y0)
     (equal y (append y0 suffix))
     (equal (len y0) (len xs))
     (equal
      pairs
      (tba-conv-zip xs (reverse y0))))))

;; In the nonempty recursive branch, every result satisfying the recursive
;; postcondition must leave a nonempty suffix for the following pattern match.

(defun-sk tba-conv-all-recursive-results-nonempty-p (xs y)
  (forall (o1 o2)
    (implies
     (and
      (tba-conv-pair-list-p o1)
      (tba-conv-list-p o2))
     (implies
      (tba-conv-prefix-relation-p xs y o2 o1)
      (consp o2)))))

(defun tba-conv-recursive-call-condition-p (x y)
  (if (consp x)
      (let ((xs (cdr x)))
        (and
         (and
          (if (consp x)
              (equal (cdr x) xs)
            nil)
          (<= (len xs) (len y)))
         (tba-conv-all-recursive-results-nonempty-p xs y)))
    t))

;; This preserves both existential witnesses R1 and YS1 inside the nonempty
;; branch premise. The head pair is (x0, car YS1), and the remaining suffix is
;; cdr YS1.

(defun-sk tba-conv-cons-result-premise-p (x0 xs y r ys)
  (exists (r1 ys1)
    (and
     (tba-conv-pair-list-p r1)
     (tba-conv-list-p ys1)
     (tba-conv-prefix-relation-p xs y ys1 r1)
     (if (consp ys1)
         (and
          (equal
           r
           (cons
            (cons x0 (car ys1))
            r1))
          (equal ys (cdr ys1)))
       nil))))

(defun tba-conv-result-premise-p (x y r ys)
  (if (consp x)
      (tba-conv-cons-result-premise-p
       (car x) (cdr x) y r ys)
    (and
     (equal r nil)
     (equal ys y))))

;; R and YS retain their universal scope from the source verification
;; condition, while the prefix witness in the conclusion remains existential.

(defun-sk tba-conv-all-results-postcondition-p (x y)
  (forall (r ys)
    (implies
     (and
      (tba-conv-pair-list-p r)
      (tba-conv-list-p ys))
     (implies
      (tba-conv-result-premise-p x y r ys)
      (tba-conv-prefix-relation-p x y ys r)))))

(defun
  ntp4vc-pearl-there-and-back-again-convolution-convolution-recqtvc-statement
  (x y)
  (implies
   (and
    (tba-conv-element-p (tba-conv-default-element))
    (tba-conv-list-p x)
    (tba-conv-list-p y)
    (<= (len x) (len y)))
   (and
    (tba-conv-recursive-call-condition-p x y)
    (tba-conv-all-results-postcondition-p x y))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
