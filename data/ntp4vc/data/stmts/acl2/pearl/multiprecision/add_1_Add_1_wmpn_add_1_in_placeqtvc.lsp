;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/add_1_Add_1_wmpn_add_1_in_placeqtvc: the verification
;; condition for in-place addition of one 64-bit limb, including pointer
;; updates, carry invariants, framing, and loop continuations. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source pointer type and its observations are abstract.  These
;; conservative interfaces retain that abstraction; their complete source
;; typing conditions are explicit in MPADD1-INTERFACE-P below.

(defstub mpadd1-ptr-p (x) t)
(defstub mpadd1-zone-p (x) t)
(defstub mpadd1-data-length (x) t)
(defstub mpadd1-offset (x) t)
(defstub mpadd1-minimum (x) t)
(defstub mpadd1-maximum (x) t)
(defstub mpadd1-writable (x) t)
(defstub mpadd1-zone (x) t)
(defstub mpadd1-pelt (x index) t)

(defun mpadd1-uint64-p (x)
  (and
   (integerp x)
   (<= 0 x)
   (< x 18446744073709551616)))

(defun mpadd1-uint32-p (x)
  (and
   (integerp x)
   (<= 0 x)
   (< x 4294967296)))

(defun mpadd1-bool-p (x)
  (or
   (equal x t)
   (equal x nil)))

;; A 32-bit word is represented by its unsigned bit pattern.  This is the
;; exact two's-complement signed interpretation used by the source sint.

(defun mpadd1-sint32 (x)
  (if (< x 2147483648)
      x
    (- x 4294967296)))

(defun mpadd1-int32-in-bounds-p (x)
  (and
   (integerp x)
   (<= -2147483648 x)
   (<= x 2147483647)))

(defun-sk mpadd1-pointer-domain-nonempty-p ()
  (exists (x)
    (mpadd1-ptr-p x)))

(defun-sk mpadd1-interface-typed-p ()
  (forall (x index)
    (implies
     (mpadd1-ptr-p x)
     (and
      (natp (mpadd1-data-length x))
      (integerp (mpadd1-offset x))
      (integerp (mpadd1-minimum x))
      (integerp (mpadd1-maximum x))
      (mpadd1-bool-p (mpadd1-writable x))
      (mpadd1-zone-p (mpadd1-zone x))
      (implies
       (integerp index)
       (mpadd1-uint64-p
        (mpadd1-pelt x index)))))))

(defun mpadd1-interface-p ()
  (and
   (mpadd1-pointer-domain-nonempty-p)
   (mpadd1-interface-typed-p)))

;; This is Why3 C.valid specialized to pointers containing 64-bit limbs.

(defun mpadd1-valid-p (x size)
  (and
   (mpadd1-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0 (mpadd1-minimum x))
   (<= (mpadd1-minimum x)
       (mpadd1-offset x))
   (<= (+ (mpadd1-offset x) size)
       (mpadd1-maximum x))
   (<= (mpadd1-maximum x)
       (mpadd1-data-length x))))

;; The source value function is the little-endian radix-2^64 value of the
;; indicated prefix, starting at the pointer's current offset.

(defun mpadd1-value-from (x index count)
  (declare (xargs :measure (nfix count)))
  (if (zp (nfix count))
      0
    (+
     (mpadd1-pelt x index)
     (*
      18446744073709551616
      (mpadd1-value-from
       x
       (+ index 1)
       (- (nfix count) 1))))))

(defun mpadd1-value (x count)
  (mpadd1-value-from
   x
   (mpadd1-offset x)
   count))

(defun mpadd1-radix-power (exponent)
  (expt 18446744073709551616 exponent))

;; Equality of source pointer observations retained across a write.

(defun mpadd1-same-snapshot-p (new old)
  (and
   (equal
    (mpadd1-data-length new)
    (mpadd1-data-length old))
   (equal
    (mpadd1-offset new)
    (mpadd1-offset old))
   (equal
    (mpadd1-minimum new)
    (mpadd1-minimum old))
   (equal
    (mpadd1-maximum new)
    (mpadd1-maximum old))
   (equal
    (mpadd1-writable new)
    (mpadd1-writable old))
   (equal
    (mpadd1-zone new)
    (mpadd1-zone old))))

;; Extensional equality to a single map update on the full integer index
;; domain.

(defun-sk mpadd1-single-update-p
    (new old update-index value)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mpadd1-pelt new index)
      (if (equal index update-index)
          value
        (mpadd1-pelt old index))))))

;; The memory outside [offset(new), offset(new)+count) is unchanged.

(defun-sk mpadd1-frame-p (new old count)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index (mpadd1-offset new))
       (<= (+ (mpadd1-offset new) count)
           index))
      (equal
       (mpadd1-pelt new index)
       (mpadd1-pelt old index))))))

(defun mpadd1-final-state-p
    (memory old size addend carry)
  (and
   (equal
    (+
     (mpadd1-value memory size)
     (*
      (mpadd1-radix-power size)
      carry))
    (+
     (mpadd1-value old size)
     addend))
   (<= 0 carry)
   (<= carry 1)
   (mpadd1-frame-p memory old size)))

(defun mpadd1-loop-invariant-p
    (memory old index-word carry size-word addend)
  (let ((index (mpadd1-sint32 index-word))
        (size (mpadd1-sint32 size-word)))
    (and
     (<= 1 index)
     (<= index size)
     (<= 0 carry)
     (<= carry 1)
     (or
      (equal carry 1)
      (equal index-word size-word))
     (equal
      (+
       (mpadd1-value memory index)
       (*
        (mpadd1-radix-power index)
        carry))
      (+
       (mpadd1-value old index)
       addend))
     (mpadd1-frame-p memory old index))))

(defun mpadd1-initial-carry-invariant-p
    (memory old size-word addend)
  (and
   (<= 1 (mpadd1-sint32 size-word))
   (<= 0 1)
   (<= 1 1)
   (or
    (equal 1 1)
    (equal 1 size-word))
   (equal
    (+
     (mpadd1-value memory 1)
     (mpadd1-radix-power 1))
    (+
     (mpadd1-value old 1)
     addend))
   (mpadd1-frame-p memory old 1)))

;; This is the innermost source quantifier over the Boolean zero test.

(defun-sk mpadd1-o3-continuation-p
    (old size-word addend index-word carry memory res1 o2)
  (forall (o3)
    (implies
     (mpadd1-bool-p o3)
     (implies
      (and
       (implies
        (equal res1 0)
        (equal o3 t))
       (implies
        (equal o3 t)
        (equal res1 0)))
      (if (not (equal o3 t))
          (mpadd1-final-state-p
           memory
           old
           (mpadd1-sint32 size-word)
           addend
           0)
        (and
         (<= 0
             (- (mpadd1-sint32 size-word)
                (mpadd1-sint32 index-word)))
         (< (- (mpadd1-sint32 size-word)
               (mpadd1-sint32 o2))
            (- (mpadd1-sint32 size-word)
               (mpadd1-sint32 index-word)))
         (mpadd1-loop-invariant-p
          memory
          old
          o2
          carry
          size-word
          addend)))))))

(defun-sk mpadd1-o2-continuation-p
    (old size-word addend index-word carry memory res1)
  (forall (o2)
    (implies
     (mpadd1-uint32-p o2)
     (implies
      (equal
       (mpadd1-sint32 o2)
       (+ (mpadd1-sint32 index-word) 1))
      (mpadd1-o3-continuation-p
       old
       size-word
       addend
       index-word
       carry
       memory
       res1
       o2)))))

(defun-sk mpadd1-x3-continuation-p
    (old size-word addend index-word carry memory-before res1)
  (forall (memory)
    (implies
     (mpadd1-ptr-p memory)
     (implies
      (and
       (mpadd1-same-snapshot-p
        memory
        memory-before)
       (mpadd1-single-update-p
        memory
        memory-before
        (+ (mpadd1-offset memory)
           (mpadd1-sint32 index-word))
        res1)
       (equal
        (mpadd1-pelt
         memory
         (+ (mpadd1-offset memory)
            (mpadd1-sint32 index-word)))
        res1))
      (and
       (mpadd1-int32-in-bounds-p
        (+ (mpadd1-sint32 index-word) 1))
       (mpadd1-o2-continuation-p
        old
        size-word
        addend
        index-word
        carry
        memory
        res1))))))

(defun-sk mpadd1-res1-continuation-p
    (old size-word addend index-word carry memory)
  (forall (res1)
    (implies
     (mpadd1-uint64-p res1)
     (implies
      (equal
       res1
       (mod
        (+
         (mpadd1-pelt
          memory
          (+ (mpadd1-offset memory)
             (mpadd1-sint32 index-word)))
         1)
        18446744073709551616))
      (and
       (<= (mpadd1-minimum memory)
           (+ (mpadd1-offset memory)
              (mpadd1-sint32 index-word)))
       (< (+ (mpadd1-offset memory)
             (mpadd1-sint32 index-word))
          (mpadd1-maximum memory))
       (equal (mpadd1-writable memory) t)
       (mpadd1-x3-continuation-p
        old
        size-word
        addend
        index-word
        carry
        memory
        res1))))))

(defun mpadd1-loop-continuation-p
    (old size-word addend index-word carry memory)
  (if (< (mpadd1-sint32 index-word)
         (mpadd1-sint32 size-word))
      (and
       (<= (mpadd1-minimum memory)
           (+ (mpadd1-offset memory)
              (mpadd1-sint32 index-word)))
       (< (+ (mpadd1-offset memory)
             (mpadd1-sint32 index-word))
          (mpadd1-maximum memory))
       (mpadd1-res1-continuation-p
        old
        size-word
        addend
        index-word
        carry
        memory))
    (mpadd1-final-state-p
     memory
     old
     (mpadd1-sint32 size-word)
     addend
     carry)))

(defun-sk mpadd1-x2-continuation-p
    (old size-word addend memory-before)
  (forall (index-word carry memory)
    (implies
     (and
      (mpadd1-uint32-p index-word)
      (mpadd1-uint64-p carry)
      (mpadd1-ptr-p memory))
     (implies
      (and
       (mpadd1-same-snapshot-p
        memory
        memory-before)
       (mpadd1-loop-invariant-p
        memory
        old
        index-word
        carry
        size-word
        addend))
      (mpadd1-loop-continuation-p
       old
       size-word
       addend
       index-word
       carry
       memory)))))

(defun mpadd1-after-first-write-p
    (old size-word addend old-first res memory)
  (if (< res old-first)
      (and
       (mpadd1-initial-carry-invariant-p
        memory
        old
        size-word
        addend)
       (mpadd1-x2-continuation-p
        old
        size-word
        addend
        memory))
    (mpadd1-final-state-p
     memory
     old
     (mpadd1-sint32 size-word)
     addend
     0)))

(defun-sk mpadd1-x1-continuation-p
    (old size-word addend old-first res)
  (forall (memory)
    (implies
     (mpadd1-ptr-p memory)
     (implies
      (and
       (mpadd1-same-snapshot-p memory old)
       (mpadd1-single-update-p
        memory
        old
        (mpadd1-offset memory)
        res))
      (mpadd1-after-first-write-p
       old
       size-word
       addend
       old-first
       res
       memory)))))

(defun-sk mpadd1-result-continuation-p
    (old size-word addend old-first)
  (forall (res)
    (implies
     (mpadd1-uint64-p res)
     (implies
      (equal
       res
       (mod
        (+ old-first addend)
        18446744073709551616))
      (and
       (<= (mpadd1-minimum old)
           (mpadd1-offset old))
       (< (mpadd1-offset old)
          (mpadd1-maximum old))
       (equal (mpadd1-writable old) t)
       (mpadd1-x1-continuation-p
        old
        size-word
        addend
        old-first
        res))))))

(defun
  ntp4vc-pearl-multiprecision-add-1-add-1-wmpn-add-1-in-placeqtvc-statement
  (x size-word addend)
  (implies
   (and
    (mpadd1-interface-p)
    (mpadd1-ptr-p x)
    (mpadd1-uint32-p size-word)
    (mpadd1-uint64-p addend)
    (mpadd1-valid-p
     x
     (mpadd1-sint32 size-word))
    (< 0 (mpadd1-sint32 size-word))
    (equal (mpadd1-writable x) t))
   (and
    (<= (mpadd1-minimum x)
        (mpadd1-offset x))
    (< (mpadd1-offset x)
       (mpadd1-maximum x))
    (mpadd1-result-continuation-p
     x
     size-word
     addend
     (mpadd1-pelt
      x
      (mpadd1-offset x))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
