;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/multiprecision/sub_1_Sub_1_wmpn_decrqtvc: the verification condition
;; for subtracting one 64-bit limb from a nonempty multiprecision value in
;; place, including borrow-loop invariants, pointer updates, and memory framing.
;; This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source pointers remain abstract, while their data fields are represented
;; exactly as finite lists of 64-bit limbs. All source typing conditions are
;; explicit in MPDECR-INTERFACE-P.

(defstub mpdecr-ptr-p (x) t)
(defstub mpdecr-zone-p (x) t)
(defstub mpdecr-data (x) t)
(defstub mpdecr-offset (x) t)
(defstub mpdecr-minimum (x) t)
(defstub mpdecr-maximum (x) t)
(defstub mpdecr-writable (x) t)
(defstub mpdecr-zone (x) t)

(defun mpdecr-uint64-p (x)
  (and
   (integerp x)
   (<= 0 x)
   (< x 18446744073709551616)))

(defun mpdecr-uint32-p (x)
  (and
   (integerp x)
   (<= 0 x)
   (< x 4294967296)))

(defun mpdecr-bool-p (x)
  (or
   (equal x t)
   (equal x nil)))

(defun mpdecr-uint64-list-p (xs)
  (if (atom xs)
      (equal xs nil)
    (and
     (mpdecr-uint64-p (car xs))
     (mpdecr-uint64-list-p (cdr xs)))))

;; Exact two's-complement signed interpretation of a 32-bit word.

(defun mpdecr-sint32 (x)
  (if (< x 2147483648)
      x
    (- x 4294967296)))

(defun mpdecr-int32-in-bounds-p (x)
  (and
   (integerp x)
   (<= -2147483648 x)
   (<= x 2147483647)))

(defun-sk mpdecr-pointer-domain-nonempty-p ()
  (exists (x)
    (mpdecr-ptr-p x)))

(defun-sk mpdecr-interface-typed-p ()
  (forall (x)
    (implies
     (mpdecr-ptr-p x)
     (and
      (mpdecr-uint64-list-p
       (mpdecr-data x))
      (integerp (mpdecr-offset x))
      (integerp (mpdecr-minimum x))
      (integerp (mpdecr-maximum x))
      (mpdecr-bool-p
       (mpdecr-writable x))
      (mpdecr-zone-p
       (mpdecr-zone x))))))

(defun mpdecr-interface-p ()
  (and
   (mpdecr-pointer-domain-nonempty-p)
   (mpdecr-interface-typed-p)))

(defun mpdecr-data-length (x)
  (len (mpdecr-data x)))

;; The source pelts function maps negative indices through Int.toNat and uses
;; the zero limb as the default beyond the finite data list.

(defun mpdecr-pelt (x index)
  (let ((value
         (nth
          (nfix index)
          (mpdecr-data x))))
    (if (mpdecr-uint64-p value)
        value
      0)))

;; Why3 C.valid specialized to pointers containing 64-bit limbs.

(defun mpdecr-valid-p (x size)
  (and
   (mpdecr-int32-in-bounds-p size)
   (<= 0 size)
   (<= 0 (mpdecr-minimum x))
   (<= (mpdecr-minimum x)
       (mpdecr-offset x))
   (<= (+ (mpdecr-offset x) size)
       (mpdecr-maximum x))
   (<= (mpdecr-maximum x)
       (mpdecr-data-length x))))

;; Little-endian radix-2^64 value of a prefix beginning at the pointer offset.

(defun mpdecr-value-from (x index count)
  (declare (xargs :measure (nfix count)))
  (if (zp (nfix count))
      0
    (+
     (mpdecr-pelt x index)
     (*
      18446744073709551616
      (mpdecr-value-from
       x
       (+ index 1)
       (- (nfix count) 1))))))

(defun mpdecr-value (x count)
  (mpdecr-value-from
   x
   (mpdecr-offset x)
   count))

(defun mpdecr-radix-power (exponent)
  (expt 18446744073709551616 (nfix exponent)))

;; Extensional equality of source pelts maps over their full integer domain.

(defun-sk mpdecr-same-pelts-p (left right)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mpdecr-pelt left index)
      (mpdecr-pelt right index)))))

;; Exact source equality to a single functional update.

(defun-sk mpdecr-single-update-p
    (new old update-index value)
  (forall (index)
    (implies
     (integerp index)
     (equal
      (mpdecr-pelt new index)
      (if (equal index update-index)
          value
        (mpdecr-pelt old index))))))

;; Equality of every pointer observation required after C.incr.

(defun mpdecr-shifted-pointer-p
    (shifted base amount)
  (and
   (equal
    (mpdecr-offset shifted)
    (+ (mpdecr-offset base) amount))
   (equal
    (mpdecr-data-length shifted)
    (mpdecr-data-length base))
   (mpdecr-same-pelts-p shifted base)
   (equal
    (mpdecr-data shifted)
    (mpdecr-data base))
   (equal
    (mpdecr-minimum shifted)
    (mpdecr-minimum base))
   (equal
    (mpdecr-maximum shifted)
    (mpdecr-maximum base))
   (equal
    (mpdecr-zone shifted)
    (mpdecr-zone base))
   (equal
    (mpdecr-writable shifted)
    (mpdecr-writable base))))

;; Metadata equalities supplied around each source C.set operation.

(defun mpdecr-write-link-p
    (updated post-write before-write)
  (and
   (equal
    (mpdecr-data updated)
    (mpdecr-data post-write))
   (equal
    (mpdecr-data-length post-write)
    (mpdecr-data-length before-write))
   (equal
    (mpdecr-offset updated)
    (mpdecr-offset before-write))
   (equal
    (mpdecr-minimum updated)
    (mpdecr-minimum before-write))
   (equal
    (mpdecr-maximum updated)
    (mpdecr-maximum before-write))
   (equal
    (mpdecr-writable updated)
    (mpdecr-writable before-write))
   (equal
    (mpdecr-zone updated)
    (mpdecr-zone before-write))))

(defun mpdecr-snapshot-metadata-p
    (new old)
  (and
   (equal
    (mpdecr-data-length new)
    (mpdecr-data-length old))
   (equal
    (mpdecr-offset new)
    (mpdecr-offset old))
   (equal
    (mpdecr-minimum new)
    (mpdecr-minimum old))
   (equal
    (mpdecr-maximum new)
    (mpdecr-maximum old))
   (equal
    (mpdecr-writable new)
    (mpdecr-writable old))
   (equal
    (mpdecr-zone new)
    (mpdecr-zone old))))

(defun mpdecr-loop-pointer-p
    (pointer memory index)
  (and
   (equal
    (mpdecr-offset pointer)
    (+ (mpdecr-offset memory) index))
   (mpdecr-same-pelts-p pointer memory)
   (equal
    (mpdecr-data-length pointer)
    (mpdecr-data-length memory))
   (equal
    (mpdecr-minimum pointer)
    (mpdecr-minimum memory))
   (equal
    (mpdecr-maximum pointer)
    (mpdecr-maximum memory))))

;; The memory at indices from START through SIZE-1 is unchanged.

(defun-sk mpdecr-tail-unchanged-p
    (new old start size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= start index)
       (< index size))
      (equal
       (mpdecr-pelt
        new
        (+ (mpdecr-offset new)
           index))
       (mpdecr-pelt
        old
        (+ (mpdecr-offset new)
           index)))))))

;; The memory outside [offset(new), offset(new)+size) is unchanged.

(defun-sk mpdecr-frame-p (new old size)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (or
       (< index (mpdecr-offset new))
       (<= (+ (mpdecr-offset new) size)
           index))
      (equal
       (mpdecr-pelt new index)
       (mpdecr-pelt old index))))))

(defun mpdecr-final-state-p
    (memory old size-word addend)
  (let ((size (mpdecr-sint32 size-word)))
    (and
     (equal
      (mpdecr-value memory size)
      (- (mpdecr-value old size)
         addend))
     (mpdecr-frame-p memory old size))))

(defun mpdecr-initial-loop-invariant-p
    (pointer memory old size-word addend)
  (let ((size (mpdecr-sint32 size-word)))
    (and
     (and
      (<= 1 1)
      (<= 1 size))
     (mpdecr-loop-pointer-p
      pointer memory 1)
     (implies
      (equal 1 size-word)
      (equal 1 0))
     (and
      (<= 0 1)
      (<= 1 1))
     (equal
      (mpdecr-writable pointer)
      t)
     (equal
      (-
       (mpdecr-value memory 1)
       (* (mpdecr-radix-power 1) 1))
      (- (mpdecr-value old 1)
         addend))
     (mpdecr-tail-unchanged-p
      memory old 1 size)
     (mpdecr-frame-p
      memory old size))))

(defun mpdecr-loop-invariant-p
    (pointer index-word carry memory old size-word addend)
  (let ((index (mpdecr-sint32 index-word))
        (size (mpdecr-sint32 size-word)))
    (and
     (and
      (<= 1 index)
      (<= index size))
     (mpdecr-loop-pointer-p
      pointer memory index)
     (implies
      (equal index-word size-word)
      (equal carry 0))
     (and
      (<= 0 carry)
      (<= carry 1))
     (equal
      (mpdecr-writable pointer)
      t)
     (equal
      (-
       (mpdecr-value memory index)
       (*
        (mpdecr-radix-power index)
        carry))
      (- (mpdecr-value old index)
         addend))
     (mpdecr-tail-unchanged-p
      memory old index size)
     (mpdecr-frame-p
      memory old size))))

(defun mpdecr-next-loop-invariant-p
    (pointer next-index-word carry memory old index-word size-word addend)
  (let ((next-index
         (mpdecr-sint32 next-index-word))
        (index
         (mpdecr-sint32 index-word))
        (size
         (mpdecr-sint32 size-word)))
    (and
     (and
      (<= 0 (- size index))
      (< (- size next-index)
         (- size index)))
     (and
      (<= 1 next-index)
      (<= next-index size))
     (mpdecr-loop-pointer-p
      pointer memory next-index)
     (implies
      (equal next-index-word size-word)
      (equal carry 0))
     (and
      (<= 0 carry)
      (<= carry 1))
     (equal
      (mpdecr-writable pointer)
      t)
     (equal
      (-
       (mpdecr-value memory next-index)
       (*
        (mpdecr-radix-power next-index)
        carry))
      (- (mpdecr-value old next-index)
         addend))
     (mpdecr-tail-unchanged-p
      memory old next-index size)
     (mpdecr-frame-p
      memory old size))))

;; Continuation after the loop-body test of whether the old limb was zero.

(defun-sk mpdecr-o6-continuation-p
    (pointer memory old index-word next-index-word
             size-word carry addend old-limb)
  (forall (zero-test)
    (implies
     (mpdecr-bool-p zero-test)
     (implies
      (and
       (implies
        (equal old-limb 0)
        (equal zero-test t))
       (implies
        (equal zero-test t)
        (equal old-limb 0)))
      (if (not (equal zero-test t))
          (mpdecr-final-state-p
           memory old size-word addend)
        (mpdecr-next-loop-invariant-p
         pointer
         next-index-word
         carry
         memory
         old
         index-word
         size-word
         addend))))))

(defun-sk mpdecr-o5-continuation-p
    (updated post-write old index-word next-index-word
             size-word carry addend old-limb)
  (forall (pointer)
    (implies
     (mpdecr-ptr-p pointer)
     (implies
      (mpdecr-shifted-pointer-p
       pointer updated 1)
      (mpdecr-o6-continuation-p
       pointer
       post-write
       old
       index-word
       next-index-word
       size-word
       carry
       addend
       old-limb)))))

(defun-sk mpdecr-o4-continuation-p
    (updated post-write old index-word size-word
             carry addend old-limb)
  (forall (next-index-word)
    (implies
     (mpdecr-uint32-p next-index-word)
     (implies
      (equal
       (mpdecr-sint32 next-index-word)
       (+ (mpdecr-sint32 index-word) 1))
      (and
       (and
        (<=
         (mpdecr-minimum updated)
         (+ (mpdecr-offset updated) 1))
        (<=
         (+ (mpdecr-offset updated) 1)
         (mpdecr-maximum updated)))
       (mpdecr-o5-continuation-p
        updated
        post-write
        old
        index-word
        next-index-word
        size-word
        carry
        addend
        old-limb))))))

(defun-sk mpdecr-second-write-continuation-p
    (pointer memory old index-word size-word carry addend result)
  (forall (updated post-write)
    (implies
     (and
      (mpdecr-ptr-p updated)
      (mpdecr-ptr-p post-write))
     (implies
      (mpdecr-write-link-p
       updated post-write pointer)
      (implies
       (mpdecr-write-link-p
        updated post-write pointer)
       (implies
        (mpdecr-snapshot-metadata-p
         post-write memory)
        (implies
         (mpdecr-single-update-p
          updated
          pointer
          (mpdecr-offset updated)
          result)
         (and
          (mpdecr-int32-in-bounds-p
           (+ (mpdecr-sint32 index-word) 1))
          (mpdecr-o4-continuation-p
           updated
           post-write
           old
           index-word
           size-word
           carry
           addend
           (mpdecr-pelt
            pointer
            (mpdecr-offset pointer)))))))))))

(defun-sk mpdecr-second-result-continuation-p
    (pointer memory old index-word size-word carry addend)
  (forall (result)
    (implies
     (mpdecr-uint64-p result)
     (implies
      (equal
       result
       (mod
        (-
         (mpdecr-pelt
          pointer
          (mpdecr-offset pointer))
         1)
        18446744073709551616))
      (and
       (and
        (<=
         (mpdecr-minimum pointer)
         (mpdecr-offset pointer))
        (<
         (mpdecr-offset pointer)
         (mpdecr-maximum pointer)))
       (equal
        (mpdecr-writable pointer)
        t)
       (mpdecr-second-write-continuation-p
        pointer
        memory
        old
        index-word
        size-word
        carry
        addend
        result))))))

;; Continuation after testing whether the borrow limb is zero.

(defun-sk mpdecr-o3-continuation-p
    (pointer memory old index-word size-word carry addend)
  (forall (zero-test)
    (implies
     (mpdecr-bool-p zero-test)
     (implies
      (and
       (implies
        (equal carry 0)
        (equal zero-test t))
       (implies
        (equal zero-test t)
        (equal carry 0)))
      (if (not (equal zero-test t))
          (mpdecr-second-result-continuation-p
           pointer
           memory
           old
           index-word
           size-word
           carry
           addend)
        (mpdecr-final-state-p
         memory old size-word addend))))))

(defun-sk mpdecr-loop-states-p
    (initial-memory old size-word addend)
  (forall (index-word pointer carry memory)
    (implies
     (and
      (mpdecr-uint32-p index-word)
      (mpdecr-ptr-p pointer)
      (mpdecr-uint64-p carry)
      (mpdecr-ptr-p memory))
     (implies
      (mpdecr-snapshot-metadata-p
       memory initial-memory)
      (implies
       (mpdecr-loop-invariant-p
        pointer
        index-word
        carry
        memory
        old
        size-word
        addend)
       (mpdecr-o3-continuation-p
        pointer
        memory
        old
        index-word
        size-word
        carry
        addend))))))

(defun mpdecr-borrow-branch-p
    (pointer memory old size-word addend)
  (and
   (mpdecr-initial-loop-invariant-p
    pointer memory old size-word addend)
   (mpdecr-loop-states-p
    memory old size-word addend)))

(defun-sk mpdecr-first-write-continuation-p
    (shifted old size-word addend initial-limb result)
  (forall (pointer memory)
    (implies
     (and
      (mpdecr-ptr-p pointer)
      (mpdecr-ptr-p memory))
     (implies
      (mpdecr-write-link-p
       pointer memory shifted)
      (implies
       (mpdecr-snapshot-metadata-p
        memory old)
       (implies
        (mpdecr-single-update-p
         memory
         old
         (mpdecr-offset memory)
         result)
        (if (< initial-limb result)
            (mpdecr-borrow-branch-p
             pointer memory old size-word addend)
          (mpdecr-final-state-p
           memory old size-word addend))))))))

(defun-sk mpdecr-first-result-continuation-p
    (shifted old size-word addend initial-limb)
  (forall (result)
    (implies
     (mpdecr-uint64-p result)
     (implies
      (equal
       result
       (mod
        (- initial-limb addend)
        18446744073709551616))
      (and
       (and
        (<=
         (mpdecr-minimum old)
         (mpdecr-offset old))
        (<
         (mpdecr-offset old)
         (mpdecr-maximum old)))
       (equal
        (mpdecr-writable old)
        t)
       (mpdecr-first-write-continuation-p
        shifted
        old
        size-word
        addend
        initial-limb
        result))))))

(defun-sk mpdecr-shift-continuation-p
    (old size-word addend initial-limb)
  (forall (shifted)
    (implies
     (mpdecr-ptr-p shifted)
     (implies
      (mpdecr-shifted-pointer-p
       shifted old 1)
      (mpdecr-first-result-continuation-p
       shifted
       old
       size-word
       addend
       initial-limb)))))

(defun
  ntp4vc-pearl-multiprecision-sub-1-sub-1-wmpn-decrqtvc-statement
  (x size-word addend)
  (let ((size (mpdecr-sint32 size-word))
        (initial-limb
         (mpdecr-pelt x (mpdecr-offset x))))
    (implies
     (and
      (mpdecr-interface-p)
      (mpdecr-ptr-p x)
      (mpdecr-uint32-p size-word)
      (mpdecr-uint64-p addend)
      (mpdecr-valid-p x size)
      (< 0 size)
      (<= 0
          (- (mpdecr-value x size)
             addend))
      (equal
       (mpdecr-writable x)
       t))
     (and
      (<=
       (mpdecr-minimum x)
       (mpdecr-offset x))
      (<
       (mpdecr-offset x)
       (mpdecr-maximum x))
      (and
       (<=
        (mpdecr-minimum x)
        (+ (mpdecr-offset x) 1))
       (<=
        (+ (mpdecr-offset x) 1)
        (mpdecr-maximum x)))
      (mpdecr-shift-continuation-p
       x
       size-word
       addend
       initial-limb)))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
