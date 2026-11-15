;; Statement-only formalization of Logipedia corpus artifact
;; bigops.let_clause_10471 (catalog title: bigops.let_clause_10471):
;; nested isomorphism and filtered-product hypotheses imply the natural-number
;; division algorithm identity. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Tame unary function objects provide ACL2's statement-level representation
;; of the source functions nat -> nat and nat -> bool.

(defun bigops-10471-apply (function argument)
  (apply$ function (list argument)))

(defun-sk bigops-10471-nat-values-p (function)
  (forall (argument)
    (implies
     (natp argument)
     (natp (bigops-10471-apply function argument)))))

(defun bigops-10471-nat-function-p (function)
  (and
   (tamep-functionp function)
   (bigops-10471-nat-values-p function)))

(defun-sk bigops-10471-bool-values-p (function)
  (forall (argument)
    (implies
     (natp argument)
     (booleanp (bigops-10471-apply function argument)))))

(defun bigops-10471-bool-function-p (function)
  (and
   (tamep-functionp function)
   (bigops-10471-bool-values-p function)))

;; This is the natural-number specialization of bigops.bigop used by the
;; source statement: indices below BOUND whose predicate is true are
;; multiplied, with neutral element 1.

(defun bigops-10471-product (bound predicate function)
  (declare (xargs :measure (nfix bound)))
  (if (zp bound)
      1
    (let* ((index (1- bound))
           (rest
            (bigops-10471-product
             index predicate function)))
      (if (equal
           (bigops-10471-apply predicate index)
           t)
          (* (bigops-10471-apply function index)
             rest)
        rest))))

;; The source library totalizes division by zero with div(n,0) = n+1 and
;; mod(n,0) = n. For a positive divisor it uses ordinary Euclidean division.

(defun bigops-10471-div (dividend divisor)
  (if (zp divisor)
      (+ dividend 1)
    (floor dividend divisor)))

(defun bigops-10471-mod (dividend divisor)
  (if (zp divisor)
      dividend
    (mod dividend divisor)))

;; sub_hk h k n1 n2 p1 p2 f1 f2. The final two parameters are retained
;; because they occur in the source signature, although its definition does
;; not inspect them.

(defun-sk bigops-10471-sub-hk-p
    (h k n1 n2 p1 p2 f1 f2)
  (forall (index)
    (implies
     (and
      (natp index)
      (< index n1)
      (equal (bigops-10471-apply p1 index) t))
     (let ((image (bigops-10471-apply h index)))
       (and
        (< image n2)
        (equal (bigops-10471-apply p2 image) t)
        (equal
         (bigops-10471-apply k image)
         index))))))

(defun-sk bigops-10471-same-values-p
    (n1 p1 f1 f2 h)
  (forall (index)
    (implies
     (and
      (natp index)
      (< index n1)
      (equal (bigops-10471-apply p1 index) t))
     (equal
      (bigops-10471-apply f1 index)
      (bigops-10471-apply
       f2
       (bigops-10471-apply h index))))))

(defun bigops-10471-full-pairing-p
    (n1 n2 p1 p2 f1 f2 h k)
  (and
   (and
    (bigops-10471-same-values-p n1 p1 f1 f2 h)
    (bigops-10471-sub-hk-p
     h k n1 n2 p1 p2 f1 f2))
   (bigops-10471-sub-hk-p
    k h n2 n1 p2 p1 f2 f1)))

(defun bigops-10471-forward-pairing-p
    (n1 n2 p1 p2 f1 f2 h k)
  (and
   (bigops-10471-same-values-p n1 p1 f1 f2 h)
   (bigops-10471-sub-hk-p
    h k n1 n2 p1 p2 f1 f2)))

(defun-sk bigops-10471-iso-p
    (n1 n2 p1 p2 f1 f2)
  (exists (h k)
    (and
     (bigops-10471-nat-function-p h)
     (bigops-10471-nat-function-p k)
     (bigops-10471-full-pairing-p
      n1 n2 p1 p2 f1 f2 h k))))

(defun-sk bigops-10471-k-exists-p
    (n1 n2 p1 p2 f1 f2 h)
  (exists (k)
    (and
     (bigops-10471-nat-function-p k)
     (bigops-10471-full-pairing-p
      n1 n2 p1 p2 f1 f2 h k))))

;; This is the source's universally quantified premise over the Boolean
;; function f. The explicit 0 <= n1 hypothesis is preserved.

(defun-sk bigops-10471-product-premise-p
    (n1 p1 f1 f2 h k m)
  (forall (f)
    (implies
     (bigops-10471-bool-function-p f)
     (implies
      (<= 0 n1)
      (implies
       (bigops-10471-sub-hk-p
        h k 0 m p1 f f1 f2)
       (implies
        (bigops-10471-sub-hk-p
         k h m 0 f p1 f2 f1)
        (equal
         (bigops-10471-product 0 p1 f1)
         (bigops-10471-product m f f2))))))))

(defun-sk bigops-10471-division-identity-p ()
  (forall (x2571 x2572)
    (implies
     (and (natp x2571) (natp x2572))
     (equal
      x2571
      (+
       (* x2572
          (bigops-10471-div x2571 x2572))
       (bigops-10471-mod x2571 x2572))))))

(defun-sk bigops-10471-p20-clause-p
    (n1 p1 f1 f2 h k m)
  (forall (p20)
    (implies
     (bigops-10471-bool-function-p p20)
     (implies
      (<= 0 n1)
      (implies
       (bigops-10471-sub-hk-p
        h k 0 (+ m 1) p1 p20 f1 f2)
       (implies
        (bigops-10471-sub-hk-p
         k h (+ m 1) 0 p20 p1 f2 f1)
        (bigops-10471-division-identity-p)))))))

;; INNER-INDEX is intentionally quantified although it is not used after its
;; binder, matching the source statement's forall i, forall m scope.

(defun-sk bigops-10471-index-and-m-clause-p
    (n1 p1 f1 f2 h k)
  (forall (inner-index m)
    (implies
     (and (natp inner-index) (natp m))
     (implies
      (bigops-10471-product-premise-p
       n1 p1 f1 f2 h k m)
      (bigops-10471-p20-clause-p
       n1 p1 f1 f2 h k m)))))

(defun-sk bigops-10471-k-clause-p
    (n1 n2 p1 p2 f1 f2 h)
  (forall (k)
    (implies
     (bigops-10471-nat-function-p k)
     (implies
      (bigops-10471-full-pairing-p
       n1 n2 p1 p2 f1 f2 h k)
      (implies
       (bigops-10471-forward-pairing-p
        n1 n2 p1 p2 f1 f2 h k)
       (implies
        (bigops-10471-same-values-p n1 p1 f1 f2 h)
        (bigops-10471-index-and-m-clause-p
         n1 p1 f1 f2 h k)))))))

(defun-sk bigops-10471-h-clause-p
    (n1 n2 p1 p2 f1 f2)
  (forall (h)
    (implies
     (bigops-10471-nat-function-p h)
     (implies
      (bigops-10471-k-exists-p
       n1 n2 p1 p2 f1 f2 h)
      (bigops-10471-k-clause-p
       n1 n2 p1 p2 f1 f2 h)))))

(defun logipedia-bigops-let-clause-10471-statement
    (n1 n2 p1 p2 f1 f2)
  (implies
   (and
    (natp n1)
    (natp n2)
    (bigops-10471-bool-function-p p1)
    (bigops-10471-bool-function-p p2)
    (bigops-10471-nat-function-p f1)
    (bigops-10471-nat-function-p f2))
   (implies
    (bigops-10471-iso-p n1 n2 p1 p2 f1 f2)
    (bigops-10471-h-clause-p
     n1 n2 p1 p2 f1 f2))))

(value-triple :itpeval-statement-checked)
:q
