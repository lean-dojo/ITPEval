;; Statement-only formalization of PutnamBench corpus artifact putnam_1994_a6:
;; ten integer permutations whose nonempty finite compositions reach every
;; integer from zero have at most 512 distinct optional ordered compositions
;; stabilizing any nonempty finite integer set. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A conservative DEFSTUB supplies ten arbitrary unary functions through the
;; first argument. Proving the resulting theorem permits ordinary ACL2
;; functional instantiation for any concrete family of ten functions.
(defstub p94a6-generator (index x) t)

(defun p94a6-apply (index x)
  (p94a6-generator index x))

(defun-sk p94a6-integer-function-values-p (index)
  (forall (x)
    (implies
     (integerp x)
     (integerp (p94a6-apply index x)))))

(defun-sk p94a6-injective-on-integers-p (index)
  (forall (x y)
    (implies
     (and
      (integerp x)
      (integerp y)
      (equal (p94a6-apply index x)
             (p94a6-apply index y)))
     (equal x y))))

(defun-sk p94a6-integer-preimage-exists-p (index y)
  (exists (x)
    (and
     (integerp x)
     (equal (p94a6-apply index x) y))))

(defun-sk p94a6-surjective-on-integers-p (index)
  (forall (y)
    (implies
     (integerp y)
     (p94a6-integer-preimage-exists-p index y))))

(defun p94a6-integer-permutation-p (index)
  (and
   (natp index)
   (< index 10)
   (p94a6-integer-function-values-p index)
   (p94a6-injective-on-integers-p index)
   (p94a6-surjective-on-integers-p index)))

(defun p94a6-index-word-p (word)
  (if (endp word)
      (equal word nil)
    (and
     (natp (car word))
     (< (car word) 10)
     (p94a6-index-word-p (cdr word)))))

;; The head of WORD is the outermost function, matching
;; f_i1 o f_i2 o ... o f_im.
(defun p94a6-apply-word (word x)
  (if (endp word)
      x
    (p94a6-apply
     (car word)
     (p94a6-apply-word (cdr word) x))))

(defun-sk p94a6-reaching-word-exists-p (n)
  (exists (word)
    (and
     (consp word)
     (true-listp word)
     (p94a6-index-word-p word)
     (equal (p94a6-apply-word word 0) n))))

(defun-sk p94a6-zero-orbit-is-all-integers-p ()
  (forall (n)
    (implies
     (integerp n)
     (p94a6-reaching-word-exists-p n))))

(defun p94a6-mask-bit-p (mask index)
  (equal
   (mod (floor mask (expt 2 index)) 2)
   1))

(defun p94a6-apply-optional-composition (mask x)
  (let*
      ((x9 (if (p94a6-mask-bit-p mask 9)
               (p94a6-apply 9 x)
             x))
       (x8 (if (p94a6-mask-bit-p mask 8)
               (p94a6-apply 8 x9)
             x9))
       (x7 (if (p94a6-mask-bit-p mask 7)
               (p94a6-apply 7 x8)
             x8))
       (x6 (if (p94a6-mask-bit-p mask 6)
               (p94a6-apply 6 x7)
             x7))
       (x5 (if (p94a6-mask-bit-p mask 5)
               (p94a6-apply 5 x6)
             x6))
       (x4 (if (p94a6-mask-bit-p mask 4)
               (p94a6-apply 4 x5)
             x5))
       (x3 (if (p94a6-mask-bit-p mask 3)
               (p94a6-apply 3 x4)
             x4))
       (x2 (if (p94a6-mask-bit-p mask 2)
               (p94a6-apply 2 x3)
             x3))
       (x1 (if (p94a6-mask-bit-p mask 1)
               (p94a6-apply 1 x2)
             x2))
       (x0 (if (p94a6-mask-bit-p mask 0)
               (p94a6-apply 0 x1)
             x1)))
    x0))

(defun p94a6-integer-list-p (list)
  (if (endp list)
      (equal list nil)
    (and
     (integerp (car list))
     (p94a6-integer-list-p (cdr list)))))

(defun p94a6-valid-finite-set-p (set)
  (and
   (consp set)
   (true-listp set)
   (p94a6-integer-list-p set)
   (no-duplicatesp-equal set)))

(defun-sk p94a6-image-contains-p (mask set y)
  (exists (x)
    (and
     (integerp x)
     (member-equal x set)
     (equal y (p94a6-apply-optional-composition mask x)))))

(defun-sk p94a6-stabilizes-p (mask set)
  (forall (y)
    (implies
     (integerp y)
     (iff
      (p94a6-image-contains-p mask set y)
      (member-equal y set)))))

(defun-sk p94a6-optional-functions-differ-p (left-mask right-mask)
  (exists (x)
    (and
     (integerp x)
     (not
      (equal
       (p94a6-apply-optional-composition left-mask x)
       (p94a6-apply-optional-composition right-mask x))))))

(defun p94a6-valid-mask-p (mask)
  (and
   (natp mask)
   (< mask 1024)))

(defun p94a6-all-masks-stabilize-p (masks set)
  (if (endp masks)
      (equal masks nil)
    (and
     (p94a6-valid-mask-p (car masks))
     (p94a6-stabilizes-p (car masks) set)
     (p94a6-all-masks-stabilize-p (cdr masks) set))))

(defun p94a6-mask-differs-from-list-p (mask masks)
  (if (endp masks)
      (equal masks nil)
    (and
     (p94a6-optional-functions-differ-p mask (car masks))
     (p94a6-mask-differs-from-list-p mask (cdr masks)))))

(defun p94a6-pairwise-distinct-functions-p (masks)
  (if (endp masks)
      (equal masks nil)
    (and
     (p94a6-mask-differs-from-list-p (car masks) (cdr masks))
     (p94a6-pairwise-distinct-functions-p (cdr masks)))))

;; A family has cardinality at most 512 exactly when it has no list of 513
;; pairwise extensionally distinct members.
(defun-sk p94a6-513-distinct-stabilizers-exist-p (set)
  (exists (masks)
    (and
     (true-listp masks)
     (equal (len masks) 513)
     (p94a6-all-masks-stabilize-p masks set)
     (p94a6-pairwise-distinct-functions-p masks))))

(defun p94a6-at-most-512-stabilizers-p (set)
  (not (p94a6-513-distinct-stabilizers-exist-p set)))

(defun p94a6-all-generators-are-permutations-p (index)
  (if (zp index)
      t
    (and
     (p94a6-integer-permutation-p (- index 1))
     (p94a6-all-generators-are-permutations-p (- index 1)))))

(defun p94a6-hypotheses-p ()
  (and
   (p94a6-all-generators-are-permutations-p 10)
   (p94a6-zero-orbit-is-all-integers-p)))

(defun-sk putnambench-putnam-1994-a6-statement ()
  (forall (set)
    (implies
     (and
      (p94a6-hypotheses-p)
      (p94a6-valid-finite-set-p set))
     (p94a6-at-most-512-stabilizers-p set))))

(value-triple :itpeval-statement-checked)
:q
