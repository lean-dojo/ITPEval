;; Statement-only formalization of NTP4VC corpus artifact
;; pearl/bitwalker_Bitwalker_peekthenpokeqtvc: the bitwalker verification
;; condition for reading bits from a byte stream, writing them back, and
;; preserving the resulting stream. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Bounded natural representatives are in bijection with the source unsigned
;; fixed-width words.

(defun ptp-bv8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

(defun ptp-bv32-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 4294967296)))

(defun ptp-bv64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; A proper list of 8-bit representatives is exactly a source byte stream.

(defun ptp-byte-list-p (stream)
  (if (consp stream)
      (and
       (ptp-bv8-p (car stream))
       (ptp-byte-list-p (cdr stream)))
    (equal stream nil)))

;; Int.toNat maps negative integers to zero. Source list lookup returns the
;; inhabited default byte zero outside the list.

(defun ptp-int-to-nat (value)
  (if (and (integerp value) (< value 0))
      0
    (nfix value)))

(defun ptp-nth-byte (stream index)
  (let ((byte (nth (ptp-int-to-nat index) stream)))
    (if (ptp-bv8-p byte) byte 0)))

;; For positive divisor 8, floor and mod are the source Euclidean quotient and
;; remainder. Boolean bits are represented by ACL2's t and nil.

(defun ptp-nth8-stream (stream position)
  (logbitp
   (ptp-int-to-nat (- 7 (mod position 8)))
   (ptp-nth-byte stream (floor position 8))))

(defun ptp-bit64 (word index)
  (logbitp (ptp-int-to-nat index) word))

;; This is the unsigned representative of the 64-bit word obtained by shifting
;; one left by the zero-extended 32-bit length.

(defun ptp-maxvalue (len)
  (if (< (nfix len) 64)
      (ash 1 (nfix len))
    0))

;; The low len bits of value are the selected source bits in reverse order.

(defun-sk ptp-value-low-bits-p (value addr start len)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= 0 i)
       (< i len))
      (equal
       (ptp-bit64 value i)
       (ptp-nth8-stream
        addr
        (- (- (+ start len) i) 1)))))))

;; Every remaining bit of the 64-bit value is false.

(defun-sk ptp-value-high-bits-zero-p (value len)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= len i)
       (< i 64))
      (equal (ptp-bit64 value i) nil)))))

(defun ptp-value-description-p (value addr start len)
  (and
   (implies
    (< (* 8 (len addr)) (+ start len))
    (equal value 0))
   (implies
    (<= (+ start len) (* 8 (len addr)))
    (and
     (ptp-value-low-bits-p value addr start len)
     (ptp-value-high-bits-zero-p value len)))))

;; The prefix preceding the written interval is unchanged.

(defun-sk ptp-prefix-unchanged-p (addr addr1 start)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= 0 i)
       (< i start))
      (equal
       (ptp-nth8-stream addr i)
       (ptp-nth8-stream addr1 i))))))

;; The selected interval of addr1 contains the corresponding bits of value.

(defun-sk ptp-written-interval-p (addr1 value start len)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= start i)
       (< i (+ start len)))
      (equal
       (ptp-nth8-stream addr1 i)
       (ptp-bit64
        value
        (+ (- (- len i) 1) start)))))))

;; The suffix following the written interval is unchanged.

(defun-sk ptp-suffix-unchanged-p (addr addr1 start len)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= (+ start len) i)
       (< i (* 8 (len addr1))))
      (equal
       (ptp-nth8-stream addr1 i)
       (ptp-nth8-stream addr i))))))

(defun ptp-successful-write-p (addr addr1 value start len)
  (and
   (ptp-prefix-unchanged-p addr addr1 start)
   (ptp-written-interval-p addr1 value start len)
   (ptp-suffix-unchanged-p addr addr1 start len)))

;; The final postcondition requires equality at every bit position in addr1.

(defun-sk ptp-streams-equal-p (addr addr1)
  (forall (i)
    (implies
     (integerp i)
     (implies
      (and
       (<= 0 i)
       (< i (* 8 (len addr1))))
      (equal
       (ptp-nth8-stream addr1 i)
       (ptp-nth8-stream addr i))))))

;; Direct encoding of the antecedent governing each integer return code.

(defun ptp-result-description-p (res addr addr1 value start len)
  (and
   (<= -2 res)
   (<= res 0)
   (iff
    (equal res -1)
    (< (* 8 (len addr1)) (+ start len)))
   (iff
    (equal res -2)
    (and
     (<= (ptp-maxvalue len) value)
     (<= (+ start len) (* 8 (len addr1)))))
   (iff
    (equal res 0)
    (and
     (< value (ptp-maxvalue len))
     (<= (+ start len) (* 8 (len addr1)))))
   (implies
    (equal res 0)
    (ptp-successful-write-p addr addr1 value start len))))

;; Preserve the source quantification over every mathematical integer result.

(defun-sk ptp-all-results-p (addr addr1 value start len)
  (forall (res)
    (implies
     (integerp res)
     (implies
      (ptp-result-description-p res addr addr1 value start len)
      (and
       (equal res 0)
       (ptp-streams-equal-p addr addr1))))))

;; Preserve the source quantification over every byte stream of equal length.

(defun-sk ptp-all-updated-streams-p (addr value start len)
  (forall (addr1)
    (implies
     (ptp-byte-list-p addr1)
     (implies
      (equal (len addr1) (len addr))
      (ptp-all-results-p addr addr1 value start len)))))

(defun ptp-value-postcondition-p (addr value start len)
  (and
   (< len 64)
   (< (+ start len) 4294967296)
   (< (* 8 (len addr)) 4294967296)
   (ptp-all-updated-streams-p addr value start len)))

;; Preserve the source quantification over every unsigned 64-bit value.

(defun-sk ptp-all-values-p (addr start len)
  (forall (value)
    (implies
     (ptp-bv64-p value)
     (implies
      (ptp-value-description-p value addr start len)
      (ptp-value-postcondition-p addr value start len)))))

(defun
    ntp4vc-pearl-bitwalker-bitwalker-peekthenpokeqtvc-statement
    (addr len start)
  (implies
   (and
    (ptp-byte-list-p addr)
    (ptp-bv32-p len)
    (ptp-bv32-p start)
    (< (* 8 (len addr)) 4294967296)
    (<= 0 len)
    (< len 64)
    (<= (+ start len) (* 8 (len addr))))
   (and
    (<= len 64)
    (< (+ start len) 4294967296)
    (< (* 8 (len addr)) 4294967296)
    (ptp-all-values-p addr start len))))

(value-triple :itpeval-statement-checked)
:q
