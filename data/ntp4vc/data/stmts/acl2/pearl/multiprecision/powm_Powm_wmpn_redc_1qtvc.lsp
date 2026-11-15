;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/powm_Powm_wmpn_redc_1qtvc: the verification condition
;; for one-limb Montgomery reduction of a double-width multiprecision integer,
;; including its loop invariant and final conditional subtraction.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

(defconst *wr1-radix* 18446744073709551616)

;; Canonical integers in [0, 2^w) represent the source fixed-width words.

(defun wr1-bv32-p (word)
  (and
   (integerp word)
   (<= 0 word)
   (< word 4294967296)))

(defun wr1-bv64-p (word)
  (and
   (integerp word)
   (<= 0 word)
   (< word *wr1-radix*)))

(defun wr1-sint32 (word)
  (if (< word 2147483648)
      word
    (- word 4294967296)))

(defun wr1-int32-in-bounds-p (value)
  (and
   (integerp value)
   (<= -2147483648 value)
   (<= value 2147483647)))

;; Pointers and zones remain arbitrary inhabited source carriers.  The
;; conservative selectors expose exactly the observations in this VC.

(defstub wr1-pointer-p (pointer) t)
(defstub wr1-zone-p (zone) t)
(defstub wr1-data (pointer) t)
(defstub wr1-offset (pointer) t)
(defstub wr1-minimum (pointer) t)
(defstub wr1-maximum (pointer) t)
(defstub wr1-writable (pointer) t)
(defstub wr1-zone (pointer) t)

(defun wr1-bv64-list-p (values)
  (if (consp values)
      (and
       (wr1-bv64-p (car values))
       (wr1-bv64-list-p (cdr values)))
    (equal values nil)))

(defun-sk wr1-pointer-domain-nonempty-p ()
  (exists (pointer)
    (wr1-pointer-p pointer)))

(defun-sk wr1-pointer-selectors-typed-p ()
  (forall (pointer)
    (implies
     (wr1-pointer-p pointer)
     (and
      (wr1-bv64-list-p
       (wr1-data pointer))
      (integerp (wr1-offset pointer))
      (integerp (wr1-minimum pointer))
      (integerp (wr1-maximum pointer))
      (booleanp (wr1-writable pointer))
      (wr1-zone-p
       (wr1-zone pointer))))))

(defun wr1-interface-p ()
  (and
   (wr1-pointer-domain-nonempty-p)
   (wr1-pointer-selectors-typed-p)))

;; Int.toNat sends negative integers to zero.  Total list access uses the
;; inhabited default 64-bit word zero outside the represented data.

(defun wr1-int-to-nat (value)
  (if (and
       (integerp value)
       (< value 0))
      0
    (nfix value)))

(defun wr1-pelt (pointer index)
  (let ((word
         (nth
          (wr1-int-to-nat index)
          (wr1-data pointer))))
    (if (wr1-bv64-p word)
        word
      0)))

(defun wr1-plength (pointer)
  (len (wr1-data pointer)))

;; Exact expansion of mach.c.C.valid for signed-32 sizes.

(defun wr1-valid-p (pointer size)
  (and
   (wr1-pointer-p pointer)
   (wr1-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0 (wr1-minimum pointer))
   (<= (wr1-minimum pointer)
       (wr1-offset pointer))
   (<= (+ (wr1-offset pointer) size)
       (wr1-maximum pointer))
   (<= (wr1-maximum pointer)
       (wr1-plength pointer))))

;; Little-endian base-2^64 value of a pointer interval.

(defun wr1-value-count (pointer index count)
  (declare (xargs :measure (nfix count)))
  (if (zp (nfix count))
      0
    (+
     (wr1-pelt pointer index)
     (*
      *wr1-radix*
      (wr1-value-count
       pointer
       (+ index 1)
       (- (nfix count) 1))))))

(defun wr1-value (pointer size)
  (wr1-value-count
   pointer
   (wr1-offset pointer)
   size))

(defun wr1-ipow (base exponent)
  (expt base (nfix exponent)))

(defun wr1-redc-p (ur u n modulus)
  (equal
   (mod ur modulus)
   (mod
    (* (wr1-ipow *wr1-radix* n)
       u)
    modulus)))

;; Source equalities between integer-indexed pelts maps are extensional.

(defun-sk wr1-same-pelts-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (wr1-pelt left index)
      (wr1-pelt right index)))))

(defun wr1-same-metadata-p (left right)
  (and
   (equal (wr1-plength left)
          (wr1-plength right))
   (equal (wr1-offset left)
          (wr1-offset right))
   (equal (wr1-minimum left)
          (wr1-minimum right))
   (equal (wr1-maximum left)
          (wr1-maximum right))
   (equal (wr1-writable left)
          (wr1-writable right))
   (equal (wr1-zone left)
          (wr1-zone right))))

(defun wr1-shift-state-p (new old amount)
  (and
   (equal (wr1-offset new)
          (+ (wr1-offset old) amount))
   (equal (wr1-plength new)
          (wr1-plength old))
   (wr1-same-pelts-p new old)
   (equal (wr1-data new)
          (wr1-data old))
   (equal (wr1-minimum new)
          (wr1-minimum old))
   (equal (wr1-maximum new)
          (wr1-maximum old))
   (equal (wr1-zone new)
          (wr1-zone old))
   (equal (wr1-writable new)
          (wr1-writable old))))

(defun-sk wr1-unchanged-outside-p
    (new old start size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index start)
       (<= (+ start size) index))
      (equal
       (wr1-pelt new index)
       (wr1-pelt old index))))))

(defun-sk wr1-updated-pelts-p
    (new old update-index update-value)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (wr1-pelt new index)
      (if (equal index update-index)
          update-value
        (wr1-pelt old index))))))

;; The following predicates preserve the source continuation structure for
;; the final add-and-conditional-subtract phase.

(defun wr1-final-rp2-premise-p
    (n up rp1 rp2 o6 vm)
  (and
   (equal
    (mod
     (wr1-value rp2 (wr1-sint32 n))
     vm)
    (mod
     (+
      (wr1-value rp1 (wr1-sint32 n))
      (*
       (wr1-ipow
        *wr1-radix*
        (wr1-sint32 n))
       o6))
     vm))
   (wr1-unchanged-outside-p
    rp2 rp1
    (wr1-offset rp2)
    (wr1-sint32 n))
   (implies
    (<
     (wr1-value up (* 2 (wr1-sint32 n)))
     (*
      (wr1-ipow
       *wr1-radix*
       (wr1-sint32 n))
      vm))
    (<
     (wr1-value rp2 (wr1-sint32 n))
     (* 2 vm)))))

(defun wr1-final-rp2-conclusion-p
    (n up rp mp rp2)
  (and
   (wr1-redc-p
    (wr1-value up (* 2 (wr1-sint32 n)))
    (wr1-value rp2 (wr1-sint32 n))
    (wr1-sint32 n)
    (wr1-value mp (wr1-sint32 n)))
   (wr1-unchanged-outside-p
    rp2 rp
    (wr1-offset rp2)
    (wr1-sint32 n))
   (implies
    (<
     (wr1-value up (* 2 (wr1-sint32 n)))
     (*
      (wr1-ipow
       *wr1-radix*
       (wr1-sint32 n))
      (wr1-value mp (wr1-sint32 n))))
    (<
     (wr1-value rp2 (wr1-sint32 n))
     (* 2
        (wr1-value mp (wr1-sint32 n)))))))

(defun wr1-final-rp2-body-p
    (n up rp mp rp1 o6 vm rp2)
  (implies
   (wr1-same-metadata-p rp2 rp1)
   (implies
    (wr1-final-rp2-premise-p
     n up rp1 rp2 o6 vm)
    (wr1-final-rp2-conclusion-p
     n up rp mp rp2))))

(defun-sk wr1-all-final-rp2-p
    (n up rp mp rp1 o6 vm)
  (forall (rp2)
    (implies
     (wr1-pointer-p rp2)
     (wr1-final-rp2-body-p
      n up rp mp rp1 o6 vm rp2))))

(defun wr1-sub-b-body-p
    (n up mp rp1 rp2 o6 vm b)
  (implies
   (and
    (equal
     (-
      (wr1-value rp2 (wr1-sint32 n))
      (*
       (wr1-ipow
        *wr1-radix*
        (wr1-sint32 n))
       b))
     (-
      (wr1-value rp1 (wr1-sint32 n))
      (wr1-value mp (wr1-sint32 n))))
    (<= 0 b)
    (<= b 1)
    (wr1-unchanged-outside-p
     rp2 rp1
     (wr1-offset rp2)
     (wr1-sint32 n)))
   (and
    (equal
     (mod
      (wr1-value rp2 (wr1-sint32 n))
      vm)
     (mod
      (+
       (wr1-value rp1 (wr1-sint32 n))
       (*
        (wr1-ipow
         *wr1-radix*
         (wr1-sint32 n))
        o6))
      vm))
    (wr1-unchanged-outside-p
     rp2 rp1
     (wr1-offset rp2)
     (wr1-sint32 n))
    (implies
     (<
      (wr1-value up (* 2 (wr1-sint32 n)))
      (*
       (wr1-ipow
        *wr1-radix*
        (wr1-sint32 n))
       vm))
     (<
      (wr1-value rp2 (wr1-sint32 n))
      (* 2 vm))))))

(defun-sk wr1-all-sub-b-p
    (n up mp rp1 rp2 o6 vm)
  (forall (b)
    (implies
     (wr1-bv64-p b)
     (wr1-sub-b-body-p
      n up mp rp1 rp2 o6 vm b))))

(defun wr1-sub-rp2-body-p
    (n up mp rp1 o6 vm rp2)
  (implies
   (wr1-same-metadata-p rp2 rp1)
   (wr1-all-sub-b-p
    n up mp rp1 rp2 o6 vm)))

(defun-sk wr1-all-sub-rp2-p
    (n up mp rp1 o6 vm)
  (forall (rp2)
    (implies
     (wr1-pointer-p rp2)
     (wr1-sub-rp2-body-p
      n up mp rp1 o6 vm rp2))))

(defun wr1-no-sub-result-p
    (n up rp1 o6 vm)
  (and
   (equal
    (mod
     (wr1-value rp1 (wr1-sint32 n))
     vm)
    (mod
     (+
      (wr1-value rp1 (wr1-sint32 n))
      (*
       (wr1-ipow
        *wr1-radix*
        (wr1-sint32 n))
       o6))
     vm))
   (implies
    (<
     (wr1-value up (* 2 (wr1-sint32 n)))
     (*
      (wr1-ipow
       *wr1-radix*
       (wr1-sint32 n))
      vm))
    (<
     (wr1-value rp1 (wr1-sint32 n))
     (* 2 vm)))))

(defun wr1-o7-body-p
    (n up rp mp rp1 o6 vm o7)
  (implies
   (and
    (implies
     (equal o6 0)
     (equal o7 t))
    (implies
     (equal o7 t)
     (equal o6 0)))
   (and
    (if (not (equal o7 t))
        (and
         (<= 0 (wr1-sint32 n))
         (wr1-valid-p rp1 (wr1-sint32 n))
         (wr1-valid-p mp (wr1-sint32 n))
         (equal (wr1-writable rp1) t)
         (wr1-all-sub-rp2-p
          n up mp rp1 o6 vm))
      (wr1-no-sub-result-p
       n up rp1 o6 vm))
    (wr1-all-final-rp2-p
     n up rp mp rp1 o6 vm))))

(defun-sk wr1-all-o7-p
    (n up rp mp rp1 o6 vm)
  (forall (o7)
    (implies
     (booleanp o7)
     (wr1-o7-body-p
      n up rp mp rp1 o6 vm o7))))

(defun wr1-o6-body-p
    (n up rp mp base o5 rp1 vm o6)
  (implies
   (and
    (<= 0 o6)
    (<= o6 1)
    (equal
     (+
      (wr1-value rp1 (wr1-sint32 n))
      (*
       (wr1-ipow
        *wr1-radix*
        (wr1-sint32 n))
       o6))
     (+
      (wr1-value base (wr1-sint32 n))
      (wr1-value o5 (wr1-sint32 n))))
    (wr1-unchanged-outside-p
     rp1 rp
     (wr1-offset rp1)
     (wr1-sint32 n)))
   (wr1-all-o7-p
    n up rp mp rp1 o6 vm)))

(defun-sk wr1-all-o6-p
    (n up rp mp base o5 rp1 vm)
  (forall (o6)
    (implies
     (wr1-bv64-p o6)
     (wr1-o6-body-p
      n up rp mp base o5 rp1 vm o6))))

(defun wr1-rp1-body-p
    (n up rp mp base o5 vm rp1)
  (implies
   (wr1-same-metadata-p rp1 rp)
   (wr1-all-o6-p
    n up rp mp base o5 rp1 vm)))

(defun-sk wr1-all-rp1-p
    (n up rp mp base o5 vm)
  (forall (rp1)
    (implies
     (wr1-pointer-p rp1)
     (wr1-rp1-body-p
      n up rp mp base o5 vm rp1))))

(defun wr1-final-o5-body-p
    (n up rp mp base vm o4 o5)
  (implies
   (wr1-shift-state-p
    o5 base (wr1-sint32 o4))
   (and
    (wr1-valid-p base (wr1-sint32 n))
    (wr1-valid-p o5 (wr1-sint32 n))
    (wr1-valid-p rp (wr1-sint32 n))
    (equal (wr1-writable rp) t)
    (wr1-all-rp1-p
     n up rp mp base o5 vm))))

(defun-sk wr1-all-final-o5-p
    (n up rp mp base vm o4)
  (forall (o5)
    (implies
     (wr1-pointer-p o5)
     (wr1-final-o5-body-p
      n up rp mp base vm o4 o5))))

(defun wr1-negative-o4-body-p
    (n up rp mp base vm o4)
  (implies
   (equal
    (wr1-sint32 o4)
    (- (wr1-sint32 n)))
   (and
    (<=
     (wr1-minimum base)
     (+ (wr1-offset base)
        (wr1-sint32 o4)))
    (<=
     (+ (wr1-offset base)
        (wr1-sint32 o4))
     (wr1-maximum base))
    (wr1-all-final-o5-p
     n up rp mp base vm o4))))

(defun-sk wr1-all-negative-o4-p
    (n up rp mp base vm)
  (forall (o4)
    (implies
     (wr1-bv32-p o4)
     (wr1-negative-o4-body-p
      n up rp mp base vm o4))))

(defun wr1-u-prime-body-p
    (n up rp mp base vm o3 u-prime)
  (implies
   (wr1-shift-state-p
    u-prime base (wr1-sint32 o3))
   (and
    (wr1-int32-in-bounds-p
     (- (wr1-sint32 n)))
    (wr1-all-negative-o4-p
     n up rp mp base vm))))

(defun-sk wr1-all-u-prime-p
    (n up rp mp base vm o3)
  (forall (u-prime)
    (implies
     (wr1-pointer-p u-prime)
     (wr1-u-prime-body-p
      n up rp mp base vm o3 u-prime))))

(defun wr1-negative-o3-body-p
    (n up rp mp base vm o3)
  (implies
   (equal
    (wr1-sint32 o3)
    (- (wr1-sint32 n)))
   (and
    (<=
     (wr1-minimum base)
     (+ (wr1-offset base)
        (wr1-sint32 o3)))
    (<=
     (+ (wr1-offset base)
        (wr1-sint32 o3))
     (wr1-maximum base))
    (wr1-all-u-prime-p
     n up rp mp base vm o3))))

(defun-sk wr1-all-negative-o3-p
    (n up rp mp base vm)
  (forall (o3)
    (implies
     (wr1-bv32-p o3)
     (wr1-negative-o3-body-p
      n up rp mp base vm o3))))

(defun wr1-final-stage-p
    (n up rp mp base vm)
  (and
   (wr1-int32-in-bounds-p
    (- (wr1-sint32 n)))
   (wr1-all-negative-o3-p
    n up rp mp base vm)))

;; Loop-state arithmetic and the addmul continuation.

(defun wr1-arithmetic-invariant-p
    (n up vm added u up1 index)
  (and
   (equal
    (+
     (*
      (wr1-ipow *wr1-radix* index)
      (wr1-value
       u
       (- (+ (wr1-sint32 n)
             (wr1-sint32 n))
          index)))
     (*
      (wr1-ipow
       *wr1-radix*
       (wr1-sint32 n))
      (wr1-value up1 index)))
    (+
     (wr1-value
      up
      (+ (wr1-sint32 n)
         (wr1-sint32 n)))
     (* vm added)))
   (<= 0 added)
   (< added
      (wr1-ipow *wr1-radix* index))
   (equal
    (mod
     (+
      (*
       (wr1-ipow *wr1-radix* index)
       (wr1-value
        u
        (- (+ (wr1-sint32 n)
              (wr1-sint32 n))
           index)))
      (*
       (wr1-ipow
        *wr1-radix*
        (wr1-sint32 n))
       (wr1-value up1 index)))
     vm)
    (mod
     (wr1-value
      up
      (+ (wr1-sint32 n)
         (wr1-sint32 n)))
     vm))))

(defun wr1-loop-invariant-p
    (n up o2 vm added u up1 j)
  (let ((j1 (wr1-sint32 j)))
    (and
     (<= 0 j1)
     (<= j1 (wr1-sint32 o2))
     (equal
      (wr1-offset u)
      (+ (wr1-offset up1) j1))
     (wr1-same-pelts-p u up1)
     (equal (wr1-minimum u)
            (wr1-minimum up1))
     (equal (wr1-maximum u)
            (wr1-maximum up1))
     (equal (wr1-plength u)
            (wr1-plength up1))
     (equal (wr1-writable u) t)
     (wr1-arithmetic-invariant-p
      n up vm added u up1 j1))))

(defun wr1-next-invariant-p
    (n up vm added m j o5 up3)
  (let ((next (+ (wr1-sint32 j) 1))
        (next-added
         (+
          added
          (*
           m
           (wr1-ipow
            *wr1-radix*
            (wr1-sint32 j))))))
    (and
     (equal
      (wr1-offset o5)
      (+ (wr1-offset up3) next))
     (wr1-same-pelts-p o5 up3)
     (equal (wr1-minimum o5)
            (wr1-minimum up3))
     (equal (wr1-maximum o5)
            (wr1-maximum up3))
     (equal (wr1-plength o5)
            (wr1-plength up3))
     (equal (wr1-writable o5) t)
     (wr1-arithmetic-invariant-p
      n up vm next-added o5 up3 next))))

(defun wr1-exit-invariant-p
    (n up o2 vm added u up1)
  (let ((index (+ (wr1-sint32 o2) 1)))
    (and
     (equal
      (wr1-offset u)
      (+ (wr1-offset up1) index))
     (wr1-same-pelts-p u up1)
     (equal (wr1-minimum u)
            (wr1-minimum up1))
     (equal (wr1-maximum u)
            (wr1-maximum up1))
     (equal (wr1-plength u)
            (wr1-plength up1))
     (equal (wr1-writable u) t)
     (wr1-arithmetic-invariant-p
      n up vm added u up1 index))))

(defun wr1-addmul-state-p
    (u1 up2 u)
  (and
   (equal (wr1-data u1)
          (wr1-data up2))
   (equal (wr1-plength up2)
          (wr1-plength u))
   (equal (wr1-offset u1)
          (wr1-offset u))
   (equal (wr1-minimum u1)
          (wr1-minimum u))
   (equal (wr1-maximum u1)
          (wr1-maximum u))
   (equal (wr1-writable u1)
          (wr1-writable u))
   (equal (wr1-zone u1)
          (wr1-zone u))))

(defun wr1-next-o5-body-p
    (n up vm added m j u2 up3 o5)
  (implies
   (wr1-shift-state-p o5 u2 1)
   (wr1-next-invariant-p
    n up vm added m j o5 up3)))

(defun-sk wr1-all-next-o5-p
    (n up vm added m j u2 up3)
  (forall (o5)
    (implies
     (wr1-pointer-p o5)
     (wr1-next-o5-body-p
      n up vm added m j u2 up3 o5))))

(defun wr1-u2-up3-body-p
    (n up vm added m j u1 up2 u2 up3 o4)
  (implies
   (wr1-addmul-state-p u2 up3 u1)
   (implies
    (wr1-addmul-state-p u2 up3 u1)
    (implies
     (wr1-same-metadata-p up3 up2)
     (implies
      (wr1-updated-pelts-p
       u2 u1 (wr1-offset u2) o4)
      (and
       (<=
        (wr1-minimum u2)
        (+ (wr1-offset u2) 1))
       (<=
        (+ (wr1-offset u2) 1)
        (wr1-maximum u2))
       (wr1-all-next-o5-p
        n up vm added m j u2 up3)))))))

(defun-sk wr1-all-u2-up3-p
    (n up vm added m j u1 up2 o4)
  (forall (u2 up3)
    (implies
     (and
      (wr1-pointer-p u2)
      (wr1-pointer-p up3))
     (wr1-u2-up3-body-p
      n up vm added m j u1 up2 u2 up3 o4))))

(defun wr1-o4-body-p
    (n up mp vm added u m j u1 up2 o4)
  (implies
   (and
    (equal
     (+
      (wr1-value u1 (wr1-sint32 n))
      (*
       (wr1-ipow
        *wr1-radix*
        (wr1-sint32 n))
       o4))
     (+
      (wr1-value u (wr1-sint32 n))
      (*
       (wr1-value mp (wr1-sint32 n))
       m)))
    (wr1-unchanged-outside-p
     u1 u
     (wr1-offset u1)
     (wr1-sint32 n)))
   (and
    (<= (wr1-minimum u1)
        (wr1-offset u1))
    (< (wr1-offset u1)
       (wr1-maximum u1))
    (equal (wr1-writable u1) t)
    (wr1-all-u2-up3-p
     n up vm added m j u1 up2 o4))))

(defun-sk wr1-all-o4-p
    (n up mp vm added u m j u1 up2)
  (forall (o4)
    (implies
     (wr1-bv64-p o4)
     (wr1-o4-body-p
      n up mp vm added u m j u1 up2 o4))))

(defun wr1-u1-up2-body-p
    (n up mp vm added u up1 m j u1 up2)
  (implies
   (wr1-addmul-state-p u1 up2 u)
   (implies
    (wr1-addmul-state-p u1 up2 u)
    (implies
     (wr1-same-metadata-p up2 up1)
     (wr1-all-o4-p
      n up mp vm added u m j u1 up2)))))

(defun-sk wr1-all-u1-up2-p
    (n up mp vm added u up1 m j)
  (forall (u1 up2)
    (implies
     (and
      (wr1-pointer-p u1)
      (wr1-pointer-p up2))
     (wr1-u1-up2-body-p
      n up mp vm added u up1 m j u1 up2))))

(defun wr1-nnj-body-p
    (n up mp vm added u up1 m j o3 nnj)
  (implies
   (equal
    (wr1-sint32 nnj)
    (- (wr1-sint32 o3)
       (wr1-sint32 j)))
   (and
    (wr1-valid-p mp (wr1-sint32 n))
    (wr1-valid-p u (wr1-sint32 n))
    (equal (wr1-writable u) t)
    (wr1-all-u1-up2-p
     n up mp vm added u up1 m j))))

(defun-sk wr1-all-nnj-p
    (n up mp vm added u up1 m j o3)
  (forall (nnj)
    (implies
     (wr1-bv32-p nnj)
     (wr1-nnj-body-p
      n up mp vm added u up1 m j o3 nnj))))

(defun wr1-positive-o3-body-p
    (n up mp vm added u up1 m j o3)
  (implies
   (equal
    (wr1-sint32 o3)
    (+ (wr1-sint32 n)
       (wr1-sint32 n)))
   (and
    (wr1-int32-in-bounds-p
     (- (wr1-sint32 o3)
        (wr1-sint32 j)))
    (wr1-all-nnj-p
     n up mp vm added u up1 m j o3))))

(defun-sk wr1-all-positive-o3-p
    (n up mp vm added u up1 m j)
  (forall (o3)
    (implies
     (wr1-bv32-p o3)
     (wr1-positive-o3-body-p
      n up mp vm added u up1 m j o3))))

(defun wr1-m-body-p
    (n up mp invm vm added u up1 j m)
  (implies
   (equal
    m
    (mod
     (*
      (wr1-pelt u (wr1-offset u))
      invm)
     *wr1-radix*))
   (and
    (wr1-int32-in-bounds-p
     (+ (wr1-sint32 n)
        (wr1-sint32 n)))
    (wr1-all-positive-o3-p
     n up mp vm added u up1 m j))))

(defun-sk wr1-all-m-p
    (n up mp invm vm added u up1 j)
  (forall (m)
    (implies
     (wr1-bv64-p m)
     (wr1-m-body-p
      n up mp invm vm added u up1 j m))))

(defun wr1-j-body-p
    (n up rp mp invm o2 vm added u up1 j)
  (and
   (implies
    (wr1-loop-invariant-p
     n up o2 vm added u up1 j)
    (and
     (<= (wr1-minimum u)
         (wr1-offset u))
     (< (wr1-offset u)
        (wr1-maximum u))
     (wr1-all-m-p
      n up mp invm vm added u up1 j)))
   (implies
    (wr1-exit-invariant-p
     n up o2 vm added u up1)
    (wr1-final-stage-p
     n up rp mp u vm))))

(defun-sk wr1-all-j-p
    (n up rp mp invm o2 vm added u up1)
  (forall (j)
    (implies
     (wr1-bv32-p j)
     (wr1-j-body-p
      n up rp mp invm o2 vm added u up1 j))))

(defun wr1-loop-state-body-p
    (n up rp mp invm o2 vm added u up1)
  (implies
   (wr1-same-metadata-p up1 up)
   (wr1-all-j-p
    n up rp mp invm o2 vm added u up1)))

(defun-sk wr1-all-loop-states-p
    (n up rp mp invm o2 vm)
  (forall (added u up1)
    (implies
     (and
      (integerp added)
      (wr1-pointer-p u)
      (wr1-pointer-p up1))
     (wr1-loop-state-body-p
      n up rp mp invm o2 vm added u up1))))

(defun wr1-initial-invariant-p
    (n up o1 vm)
  (and
   (equal (wr1-offset o1)
          (+ (wr1-offset up) 0))
   (wr1-same-pelts-p o1 up)
   (equal (wr1-minimum o1)
          (wr1-minimum up))
   (equal (wr1-maximum o1)
          (wr1-maximum up))
   (equal (wr1-plength o1)
          (wr1-plength up))
   (equal (wr1-writable o1) t)
   (equal
    (+
     (*
      (wr1-ipow *wr1-radix* 0)
      (wr1-value
       o1
       (- (+ (wr1-sint32 n)
             (wr1-sint32 n))
          0)))
     (*
      (wr1-ipow
       *wr1-radix*
       (wr1-sint32 n))
      (wr1-value up 0)))
    (+
     (wr1-value
      up
      (+ (wr1-sint32 n)
         (wr1-sint32 n)))
     (* vm 0)))
   (<= 0 0)
   (< 0 (wr1-ipow *wr1-radix* 0))
   (equal
    (mod
     (+
      (*
       (wr1-ipow *wr1-radix* 0)
       (wr1-value
        o1
        (- (+ (wr1-sint32 n)
              (wr1-sint32 n))
           0)))
      (*
       (wr1-ipow
        *wr1-radix*
        (wr1-sint32 n))
       (wr1-value up 0)))
     vm)
    (mod
     (wr1-value
      up
      (+ (wr1-sint32 n)
         (wr1-sint32 n)))
     vm))))

(defun wr1-o2-body-p
    (n up rp mp invm o1 vm o2)
  (implies
   (equal
    (wr1-sint32 o2)
    (- (wr1-sint32 n) 1))
   (and
    (implies
     (<= 0 (+ (wr1-sint32 o2) 1))
     (and
      (wr1-initial-invariant-p
       n up o1 vm)
      (wr1-all-loop-states-p
       n up rp mp invm o2 vm)))
    (implies
     (< (+ (wr1-sint32 o2) 1) 0)
     (wr1-final-stage-p
      n up rp mp o1 vm)))))

(defun-sk wr1-all-o2-p
    (n up rp mp invm o1 vm)
  (forall (o2)
    (implies
     (wr1-bv32-p o2)
     (wr1-o2-body-p
      n up rp mp invm o1 vm o2))))

(defun wr1-o1-body-p
    (n up rp mp invm o1)
  (implies
   (wr1-shift-state-p o1 up 0)
   (let ((vm (wr1-value mp (wr1-sint32 n))))
     (and
      (wr1-int32-in-bounds-p
       (- (wr1-sint32 n) 1))
      (wr1-all-o2-p
       n up rp mp invm o1 vm)))))

(defun-sk wr1-all-o1-p
    (n up rp mp invm)
  (forall (o1)
    (implies
     (wr1-pointer-p o1)
     (wr1-o1-body-p
      n up rp mp invm o1))))

(defun
    ntp4vc-pearl-multiprecision-powm-powm-wmpn-redc-1qtvc-statement
    (n mp up rp invm)
  (implies
   (and
    (wr1-interface-p)
    (wr1-bv32-p n)
    (wr1-pointer-p mp)
    (wr1-pointer-p up)
    (wr1-pointer-p rp)
    (wr1-bv64-p invm)
    (< 0 (wr1-sint32 n))
    (wr1-valid-p mp (wr1-sint32 n))
    (wr1-valid-p
     up
     (* 2 (wr1-sint32 n)))
    (wr1-valid-p rp (wr1-sint32 n))
    (oddp (wr1-value mp (wr1-sint32 n)))
    (equal
     (mod
      (*
       (wr1-value mp (wr1-sint32 n))
       invm)
      *wr1-radix*)
     (- *wr1-radix* 1))
    (equal (wr1-writable up) t)
    (equal (wr1-writable rp) t))
   (and
    (<=
     (wr1-minimum up)
     (+ (wr1-offset up) 0))
    (<=
     (+ (wr1-offset up) 0)
     (wr1-maximum up))
    (wr1-all-o1-p
     n up rp mp invm))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
