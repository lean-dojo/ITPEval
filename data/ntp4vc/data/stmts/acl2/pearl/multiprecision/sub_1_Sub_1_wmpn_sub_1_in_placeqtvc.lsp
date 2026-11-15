;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/sub_1_Sub_1_wmpn_sub_1_in_placeqtvc: the verification
;; condition for in-place subtraction of one 64-bit limb, including pointer
;; updates, borrow invariants, framing, and loop continuations. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source pointer type and its observations are abstract. These
;; conservative interfaces retain that abstraction; their complete source
;; typing conditions are explicit in MPSUB1-INTERFACE-P below.

(defstub mpsub1-ptr-p (x) t)
(defstub mpsub1-zone-p (x) t)
(defstub mpsub1-data-length (x) t)
(defstub mpsub1-offset (x) t)
(defstub mpsub1-minimum (x) t)
(defstub mpsub1-maximum (x) t)
(defstub mpsub1-writable (x) t)
(defstub mpsub1-zone (x) t)
(defstub mpsub1-pelt (x index) t)

(defun mpsub1-uint64-p (x)
  (and
   (integerp x)
   (<= 0 x)
   (< x 18446744073709551616)))

(defun mpsub1-uint32-p (x)
  (and
   (integerp x)
   (<= 0 x)
   (< x 4294967296)))

(defun mpsub1-bool-p (x)
  (or
   (equal x t)
   (equal x nil)))

;; A 32-bit word is represented by its unsigned bit pattern. This is the
;; exact two's-complement signed interpretation used by the source sint.

(defun mpsub1-sint32 (x)
  (if (< x 2147483648)
      x
    (- x 4294967296)))

(defun mpsub1-int32-in-bounds-p (x)
  (and
   (integerp x)
   (<= -2147483648 x)
   (<= x 2147483647)))

(defun-sk mpsub1-pointer-domain-nonempty-p ()
  (exists (x)
    (mpsub1-ptr-p x)))

(defun-sk mpsub1-interface-typed-p ()
  (forall (x index)
    (implies
     (mpsub1-ptr-p x)
     (and
      (natp (mpsub1-data-length x))
      (integerp (mpsub1-offset x))
      (integerp (mpsub1-minimum x))
      (integerp (mpsub1-maximum x))
      (mpsub1-bool-p (mpsub1-writable x))
      (mpsub1-zone-p (mpsub1-zone x))
      (implies
       (integerp index)
       (mpsub1-uint64-p
        (mpsub1-pelt x index)))))))

(defun mpsub1-interface-p ()
  (and
   (mpsub1-pointer-domain-nonempty-p)
   (mpsub1-interface-typed-p)))

;; This is Why3 C.valid specialized to pointers containing 64-bit limbs.

(defun mpsub1-valid-p (x size)
  (and
   (mpsub1-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0 (mpsub1-minimum x))
   (<= (mpsub1-minimum x)
       (mpsub1-offset x))
   (<= (+ (mpsub1-offset x) size)
       (mpsub1-maximum x))
   (<= (mpsub1-maximum x)
       (mpsub1-data-length x))))

;; The source value function is the little-endian radix-2^64 value of the
;; indicated prefix, starting at the pointer's current offset.

(defun mpsub1-value-from (x index count)
  (declare (xargs :measure (nfix count)))
  (if (zp (nfix count))
      0
    (+
     (mpsub1-pelt x index)
     (*
      18446744073709551616
      (mpsub1-value-from
       x
       (+ index 1)
       (- (nfix count) 1))))))

(defun mpsub1-value (x count)
  (mpsub1-value-from
   x
   (mpsub1-offset x)
   count))

(defun mpsub1-radix-power (exponent)
  (expt 18446744073709551616 exponent))

;; Equality of source pointer observations retained across a write.

(defun mpsub1-same-snapshot-p (new old)
  (and
   (equal
    (mpsub1-data-length new)
    (mpsub1-data-length old))
   (equal
    (mpsub1-offset new)
    (mpsub1-offset old))
   (equal
    (mpsub1-minimum new)
    (mpsub1-minimum old))
   (equal
    (mpsub1-maximum new)
    (mpsub1-maximum old))
   (equal
    (mpsub1-writable new)
    (mpsub1-writable old))
   (equal
    (mpsub1-zone new)
    (mpsub1-zone old))))

;; Extensional equality to a single map update on the full integer index
;; domain.

(defun-sk mpsub1-single-update-p
    (new old update-index value)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mpsub1-pelt new index)
      (if (equal index update-index)
          value
        (mpsub1-pelt old index))))))

;; The memory outside [offset(new), offset(new)+count) is unchanged.

(defun-sk mpsub1-frame-p (new old count)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index (mpsub1-offset new))
       (<= (+ (mpsub1-offset new) count)
           index))
      (equal
       (mpsub1-pelt new index)
       (mpsub1-pelt old index))))))

(defun mpsub1-final-state-p
    (memory old size subtrahend borrow)
  (and
   (equal
    (-
     (mpsub1-value memory size)
     (*
      (mpsub1-radix-power size)
      borrow))
    (-
     (mpsub1-value old size)
     subtrahend))
   (<= 0 borrow)
   (<= borrow 1)
   (mpsub1-frame-p memory old size)))

(defun mpsub1-loop-invariant-p
    (memory old index-word borrow size-word subtrahend)
  (let ((index (mpsub1-sint32 index-word))
        (size (mpsub1-sint32 size-word)))
    (and
     (<= 1 index)
     (<= index size)
     (<= 0 borrow)
     (<= borrow 1)
     (or
      (equal borrow 1)
      (equal index-word size-word))
     (equal
      (-
       (mpsub1-value memory index)
       (*
        (mpsub1-radix-power index)
        borrow))
      (-
       (mpsub1-value old index)
       subtrahend))
     (mpsub1-frame-p memory old index))))

(defun mpsub1-initial-borrow-invariant-p
    (memory old size-word subtrahend)
  (and
   (<= 1 (mpsub1-sint32 size-word))
   (<= 0 1)
   (<= 1 1)
   (or
    (equal 1 1)
    (equal 1 size-word))
   (equal
    (-
     (mpsub1-value memory 1)
     (mpsub1-radix-power 1))
    (-
     (mpsub1-value old 1)
     subtrahend))
   (mpsub1-frame-p memory old 1)))

;; This is the innermost source quantifier over the Boolean zero test. Its
;; specification tests the limb before the decrement, as in the source VC.

(defun-sk mpsub1-o3-continuation-p
    (old size-word subtrahend index-word borrow
         memory-before memory o2)
  (forall (o3)
    (implies
     (mpsub1-bool-p o3)
     (implies
      (and
       (implies
        (equal
         (mpsub1-pelt
          memory-before
          (+ (mpsub1-offset memory-before)
             (mpsub1-sint32 index-word)))
         0)
        (equal o3 t))
       (implies
        (equal o3 t)
        (equal
         (mpsub1-pelt
          memory-before
          (+ (mpsub1-offset memory-before)
             (mpsub1-sint32 index-word)))
         0)))
      (if (not (equal o3 t))
          (mpsub1-final-state-p
           memory
           old
           (mpsub1-sint32 size-word)
           subtrahend
           0)
        (and
         (<= 0
             (- (mpsub1-sint32 size-word)
                (mpsub1-sint32 index-word)))
         (< (- (mpsub1-sint32 size-word)
               (mpsub1-sint32 o2))
            (- (mpsub1-sint32 size-word)
               (mpsub1-sint32 index-word)))
         (mpsub1-loop-invariant-p
          memory
          old
          o2
          borrow
          size-word
          subtrahend)))))))

(defun-sk mpsub1-o2-continuation-p
    (old size-word subtrahend index-word borrow
         memory-before memory)
  (forall (o2)
    (implies
     (mpsub1-uint32-p o2)
     (implies
      (equal
       (mpsub1-sint32 o2)
       (+ (mpsub1-sint32 index-word) 1))
      (mpsub1-o3-continuation-p
       old
       size-word
       subtrahend
       index-word
       borrow
       memory-before
       memory
       o2)))))

(defun-sk mpsub1-x3-continuation-p
    (old size-word subtrahend index-word borrow memory-before res1)
  (forall (memory)
    (implies
     (mpsub1-ptr-p memory)
     (implies
      (and
       (mpsub1-same-snapshot-p
        memory
        memory-before)
       (mpsub1-single-update-p
        memory
        memory-before
        (+ (mpsub1-offset memory)
           (mpsub1-sint32 index-word))
        res1)
       (equal
        (mpsub1-pelt
         memory
         (+ (mpsub1-offset memory)
            (mpsub1-sint32 index-word)))
        res1))
      (and
       (mpsub1-int32-in-bounds-p
        (+ (mpsub1-sint32 index-word) 1))
       (mpsub1-o2-continuation-p
        old
        size-word
        subtrahend
        index-word
        borrow
        memory-before
        memory))))))

(defun-sk mpsub1-res1-continuation-p
    (old size-word subtrahend index-word borrow memory)
  (forall (res1)
    (implies
     (mpsub1-uint64-p res1)
     (implies
      (equal
       res1
       (mod
        (-
         (mpsub1-pelt
          memory
          (+ (mpsub1-offset memory)
             (mpsub1-sint32 index-word)))
         1)
        18446744073709551616))
      (and
       (<= (mpsub1-minimum memory)
           (+ (mpsub1-offset memory)
              (mpsub1-sint32 index-word)))
       (< (+ (mpsub1-offset memory)
             (mpsub1-sint32 index-word))
          (mpsub1-maximum memory))
       (equal (mpsub1-writable memory) t)
       (mpsub1-x3-continuation-p
        old
        size-word
        subtrahend
        index-word
        borrow
        memory
        res1))))))

(defun mpsub1-loop-continuation-p
    (old size-word subtrahend index-word borrow memory)
  (if (< (mpsub1-sint32 index-word)
         (mpsub1-sint32 size-word))
      (and
       (<= (mpsub1-minimum memory)
           (+ (mpsub1-offset memory)
              (mpsub1-sint32 index-word)))
       (< (+ (mpsub1-offset memory)
             (mpsub1-sint32 index-word))
          (mpsub1-maximum memory))
       (mpsub1-res1-continuation-p
        old
        size-word
        subtrahend
        index-word
        borrow
        memory))
    (mpsub1-final-state-p
     memory
     old
     (mpsub1-sint32 size-word)
     subtrahend
     borrow)))

(defun-sk mpsub1-x2-continuation-p
    (old size-word subtrahend memory-before)
  (forall (index-word borrow memory)
    (implies
     (and
      (mpsub1-uint32-p index-word)
      (mpsub1-uint64-p borrow)
      (mpsub1-ptr-p memory))
     (implies
      (and
       (mpsub1-same-snapshot-p
        memory
        memory-before)
       (mpsub1-loop-invariant-p
        memory
        old
        index-word
        borrow
        size-word
        subtrahend))
      (mpsub1-loop-continuation-p
       old
       size-word
       subtrahend
       index-word
       borrow
       memory)))))

(defun mpsub1-after-first-write-p
    (old size-word subtrahend old-first res memory)
  (declare (ignore res))
  (if (< old-first subtrahend)
      (and
       (mpsub1-initial-borrow-invariant-p
        memory
        old
        size-word
        subtrahend)
       (mpsub1-x2-continuation-p
        old
        size-word
        subtrahend
        memory))
    (mpsub1-final-state-p
     memory
     old
     (mpsub1-sint32 size-word)
     subtrahend
     0)))

(defun-sk mpsub1-x1-continuation-p
    (old size-word subtrahend old-first res)
  (forall (memory)
    (implies
     (mpsub1-ptr-p memory)
     (implies
      (and
       (mpsub1-same-snapshot-p memory old)
       (mpsub1-single-update-p
        memory
        old
        (mpsub1-offset memory)
        res))
      (mpsub1-after-first-write-p
       old
       size-word
       subtrahend
       old-first
       res
       memory)))))

(defun-sk mpsub1-result-continuation-p
    (old size-word subtrahend old-first)
  (forall (res)
    (implies
     (mpsub1-uint64-p res)
     (implies
      (equal
       res
       (mod
        (- old-first subtrahend)
        18446744073709551616))
      (and
       (<= (mpsub1-minimum old)
           (mpsub1-offset old))
       (< (mpsub1-offset old)
          (mpsub1-maximum old))
       (equal (mpsub1-writable old) t)
       (mpsub1-x1-continuation-p
        old
        size-word
        subtrahend
        old-first
        res))))))

(defun
  ntp4vc-pearl-multiprecision-sub-1-sub-1-wmpn-sub-1-in-placeqtvc-statement
  (x size-word subtrahend)
  (implies
   (and
    (mpsub1-interface-p)
    (mpsub1-ptr-p x)
    (mpsub1-uint32-p size-word)
    (mpsub1-uint64-p subtrahend)
    (mpsub1-valid-p
     x
     (mpsub1-sint32 size-word))
    (< 0 (mpsub1-sint32 size-word))
    (equal (mpsub1-writable x) t))
   (and
    (<= (mpsub1-minimum x)
        (mpsub1-offset x))
    (< (mpsub1-offset x)
       (mpsub1-maximum x))
    (mpsub1-result-continuation-p
     x
     size-word
     subtrahend
     (mpsub1-pelt
      x
      (mpsub1-offset x))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
