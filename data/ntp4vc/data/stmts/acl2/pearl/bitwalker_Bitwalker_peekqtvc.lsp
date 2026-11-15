;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/bitwalker_Bitwalker_peekqtvc: the bitwalker peek verification
;; condition for reading a bounded run of bits from a byte stream into a
;; 64-bit word. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Natural numbers below 2^n are in bijection with the source's unsigned
;; fixed-width words.  The arithmetic operations below are the corresponding
;; modular word operations.

(defun bitwalker-bv8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun bitwalker-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun bitwalker-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

(defun bitwalker-bv32-add (left right)
  (mod (+ left right) 4294967296))

(defun bitwalker-bv32-sub (left right)
  (mod (- left right) 4294967296))

;; A proper list of 8-bit representatives is exactly a source List (BitVec 8).

(defun bitwalker-byte-list-p (stream)
  (if (endp stream)
      (equal stream nil)
    (and
     (bitwalker-bv8-p (car stream))
     (bitwalker-byte-list-p (cdr stream)))))

;; Int.toNat maps negative integers to zero.  Source list lookup returns the
;; inhabited default byte zero outside the list.

(defun bitwalker-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun bitwalker-nth-byte (stream index)
  (let ((byte (nth (bitwalker-int-to-nat index) stream)))
    (if (bitwalker-bv8-p byte) byte 0)))

;; With positive divisor 8, ACL2 floor/mod agree with the Euclidean
;; division/remainder used by the three source representations.

(defun bitwalker-nth8-stream (stream position)
  (logbitp
   (bitwalker-int-to-nat (- 7 (mod position 8)))
   (bitwalker-nth-byte stream (floor position 8))))

(defun bitwalker-bit64 (word index)
  (logbitp (bitwalker-int-to-nat index) word))

;; Zero extension preserves the unsigned representative.  Since both inputs
;; are 32-bit, their sum cannot wrap at width 128.

(defun bitwalker-overflow-disjunction-p (left right)
  (or
   (< (+ left right) 4294967296)
   (<= (+ left right) 4294967295)))

;; Bits in [lower, upper) contain the source stream segment in reverse index
;; order.  Quantification remains over every mathematical integer.

(defun-sk bitwalker-stream-range-p
    (word lower upper stream start len)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (equal
       (bitwalker-bit64 word index)
       (bitwalker-nth8-stream
        stream
        (- (- (+ start len) index) 1)))))))

;; Every bit in the indicated half-open integer interval is false.

(defun-sk bitwalker-zero-range-p (word lower upper)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= lower index)
       (< index upper))
      (equal (bitwalker-bit64 word index) nil)))))

;; The prospective next word agrees with the current word at every bit except
;; the selected update position.

(defun-sk bitwalker-equal-except-p
    (next current excluded)
  (forall (index)
    (implies
     (integerp index)
     (implies
      (and
       (<= 0 index)
       (< index 64)
       (not (equal index excluded)))
      (equal
       (bitwalker-bit64 next index)
       (bitwalker-bit64 current index))))))

;; This is the universally quantified postcondition for writing the next
;; stream bit into the selected position of a 64-bit word.

(defun-sk bitwalker-after-write-p
    (len start stream lstart i retval)
  (forall (next)
    (implies
     (bitwalker-bv64-p next)
     (let*
         ((start-plus-i (bitwalker-bv32-add start i))
          (lstart-plus-i (bitwalker-bv32-add lstart i))
          (excluded (- 63 lstart-plus-i))
          (i-plus-one (bitwalker-bv32-add i 1)))
       (implies
        (and
         (bitwalker-equal-except-p next retval excluded)
         (equal
          (bitwalker-nth8-stream stream start-plus-i)
          (bitwalker-bit64 next excluded)))
        (and
         (bitwalker-overflow-disjunction-p i 1)
         (implies
          (equal i-plus-one (+ i 1))
          (and
           (and
            (<= 0 (- len i))
            (< (- len i-plus-one) (- len i)))
           (and
            (<= 0 i-plus-one)
            (<= i-plus-one len))
           (bitwalker-stream-range-p
            next (- len i-plus-one) len stream start len)
           (bitwalker-zero-range-p
            next 0 (- len i-plus-one))
           (bitwalker-zero-range-p
            next len 64)))))))))

;; Direct encoding of the loop continuation for a source-typed index and
;; accumulator word.

(defun bitwalker-loop-step-p
    (len start stream lstart i retval)
  (if (< i len)
      (and
       (bitwalker-overflow-disjunction-p start i)
       (implies
        (equal
         (bitwalker-bv32-add start i)
         (+ start i))
        (and
         (and
          (< (* 8 (len stream)) 4294967296)
          (<
           (bitwalker-bv32-add start i)
           (* 8 (len stream))))
         (bitwalker-overflow-disjunction-p lstart i)
         (implies
          (equal
           (bitwalker-bv32-add lstart i)
           (+ lstart i))
          (and
           (< (bitwalker-bv32-add lstart i) 64)
           (bitwalker-after-write-p
            len start stream lstart i retval))))))
    (and
     (implies
      (< (* 8 (len stream)) (+ start len))
      (equal retval 0))
     (implies
      (<= (+ start len) (* 8 (len stream)))
      (and
       (bitwalker-stream-range-p
        retval 0 len stream start len)
       (bitwalker-zero-range-p retval len 64))))))

;; Preserve the source universal quantifiers over every 32-bit loop index and
;; every 64-bit accumulator satisfying the displayed loop invariant.

(defun-sk bitwalker-loop-continuation-p
    (len start stream lstart)
  (forall (i retval)
    (implies
     (and
      (bitwalker-bv32-p i)
      (bitwalker-bv64-p retval))
     (implies
      (and
       (and
        (<= 0 i)
        (<= i len))
       (bitwalker-stream-range-p
        retval (- len i) len stream start len)
       (bitwalker-zero-range-p retval 0 (- len i))
       (bitwalker-zero-range-p retval len 64))
      (bitwalker-loop-step-p
       len start stream lstart i retval)))))

(defun
    ntp4vc-pearl-bitwalker-bitwalker-peekqtvc-statement
    (len start addr)
  (implies
   (and
    (bitwalker-bv32-p len)
    (bitwalker-bv32-p start)
    (bitwalker-byte-list-p addr)
    (<= len 64)
    (< (+ start len) 4294967296)
    (< (* 8 (len addr)) 4294967296))
   (and
    (bitwalker-overflow-disjunction-p start len)
    (implies
     (equal
      (bitwalker-bv32-add start len)
      (+ start len))
     (if
         (<
          (* 8 (len addr))
          (bitwalker-bv32-add start len))
         (implies
          (<= (+ start len) (* 8 (len addr)))
          (and
           (bitwalker-stream-range-p
            0 0 len addr start len)
           (bitwalker-zero-range-p 0 len 64)))
       (and
        (or
         (<= len 64)
         (<= len 64))
        (let ((lstart (bitwalker-bv32-sub 64 len)))
          (implies
           (equal lstart (- 64 len))
           (and
            (and
             (and
              (<= 0 0)
              (<= 0 len))
             (bitwalker-stream-range-p
              0 (- len 0) len addr start len)
             (bitwalker-zero-range-p 0 0 (- len 0))
             (bitwalker-zero-range-p 0 len 64))
            (bitwalker-loop-continuation-p
             len start addr lstart))))))))))

(value-triple :itpeval-statement-checked)
:q
