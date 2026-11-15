;; Statement-only formalization of NTP4VC corpus artifact
;; frama_c/verker/strreplace_Why3_ide_VCstrreplace_loop_inv_preserved_goal4:
;; preservation of strreplace string validity after the conditional character
;; replacement and loop-address advance, under the stated memory, address,
;; character-range, and loop-invariant hypotheses. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Source addresses are exactly pairs of mathematical integers.

(defun srg4-address-p (address)
  (and
   (consp address)
   (integerp (car address))
   (integerp (cdr address))))

(defun srg4-address-base (address)
  (car address))

(defun srg4-address-offset (address)
  (cdr address))

(defun srg4-shift (address amount)
  (cons
   (srg4-address-base address)
   (+ (srg4-address-offset address)
      amount)))

;; Conservative interfaces represent the universally arbitrary source
;; memories t_1, t_2, and t_3 and allocation map t, together with the source
;; region, address-order, logical strlen, unsigned conversion, linkedness, and
;; constancy symbols.

(defstub srg4-t1 (address) t)
(defstub srg4-t2 (address) t)
(defstub srg4-t3 (address) t)
(defstub srg4-allocation (index) t)
(defstub srg4-region (base) t)
(defstub srg4-addr-le-op (left right) t)
(defstub srg4-addr-lt-op (left right) t)
(defstub srg4-l-strlen-t2 (address) t)
(defstub srg4-to-uint64 (value) t)
(defstub srg4-linked-op () t)
(defstub srg4-sconst-op () t)

;; Preserve the source function types over the full address and unbounded
;; mathematical-integer domains.

(defun-sk srg4-function-types-p ()
  (forall (address index base value)
    (and
     (implies
      (srg4-address-p address)
      (and
       (integerp
        (srg4-t1 address))
       (integerp
        (srg4-t2 address))
       (integerp
        (srg4-t3 address))
       (integerp
        (srg4-l-strlen-t2 address))))
     (implies
      (integerp index)
      (integerp
       (srg4-allocation index)))
     (implies
      (integerp base)
      (integerp
       (srg4-region base)))
     (implies
      (integerp value)
      (integerp
       (srg4-to-uint64 value))))))

(defun srg4-addr-le-p (left right)
  (if (srg4-addr-le-op left right) t nil))

(defun srg4-addr-lt-p (left right)
  (if (srg4-addr-lt-op left right) t nil))

;; On addresses with equal bases, the source address relations are exactly
;; mathematical-integer order on offsets.

(defun-sk srg4-address-order-laws-p ()
  (forall (left right)
    (implies
     (and
      (srg4-address-p left)
      (srg4-address-p right)
      (equal
       (srg4-address-base left)
       (srg4-address-base right)))
     (and
      (equal
       (srg4-addr-le-p left right)
       (<=
        (srg4-address-offset left)
        (srg4-address-offset right)))
      (equal
       (srg4-addr-lt-p left right)
       (<
        (srg4-address-offset left)
        (srg4-address-offset right)))))))

(defun srg4-linked-p ()
  (if (srg4-linked-op) t nil))

(defun srg4-sconst-p ()
  (if (srg4-sconst-op) t nil))

;; Exact mathematical ranges for the source C integer predicates.

(defun srg4-is-sint8-p (value)
  (and
   (integerp value)
   (<= -128 value)
   (< value 128)))

(defun srg4-is-uint64-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 18446744073709551616)))

;; Universal range, identity-on-range, and projection laws for the source's
;; abstract Cint.to_uint64 operation used by the logical strlen recurrence.

(defun-sk srg4-to-uint64-laws-p ()
  (forall (value)
    (implies
     (integerp value)
     (and
      (srg4-is-uint64-p
       (srg4-to-uint64 value))
      (implies
       (srg4-is-uint64-p value)
       (equal
        (srg4-to-uint64 value)
        value))
      (equal
       (srg4-to-uint64
        (srg4-to-uint64 value))
       (srg4-to-uint64 value))))))

;; Exact unfoldings of Memory.valid_rw and Memory.separated.

(defun srg4-valid-rw-p (address length)
  (implies
   (< 0 length)
   (and
    (< 0
       (srg4-address-base address))
    (<= 0
        (srg4-address-offset address))
    (<=
     (+ (srg4-address-offset address)
        length)
     (srg4-allocation
      (srg4-address-base address))))))

(defun srg4-separated-p
    (left left-length right right-length)
  (or
   (<= left-length 0)
   (<= right-length 0)
   (not
    (equal
     (srg4-address-base left)
     (srg4-address-base right)))
   (<=
    (+ (srg4-address-offset right)
       right-length)
    (srg4-address-offset left))
   (<=
    (+ (srg4-address-offset left)
       left-length)
    (srg4-address-offset right))))

;; Exact pointwise content of Memory.havoc_access for
;; havoc t_1 t_2 (shift a_1 0) length.

(defun srg4-a3-read (address a1 length)
  (let
      ((start
        (srg4-shift a1 0)))
    (if
        (srg4-separated-p
         address 1 start length)
        (srg4-t2 address)
      (srg4-t1 address))))

;; Exact unfolding of A_Strlen.p_valid_str for t_2. The terminating position
;; remains an internal existential over all mathematical integers, and its
;; character condition remains universal over all integers.

(defun-sk srg4-t2-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (srg4-is-sint8-p
       (srg4-t2
        (srg4-shift address position)))))))

(defun-sk srg4-t2-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (srg4-t2
       (srg4-shift address index))
      0)
     (srg4-is-uint64-p index)
     (srg4-valid-rw-p
      (srg4-shift address 0)
      (+ 1 index))
     (srg4-t2-chars-sint8-through-p
      address index))))

;; Exact unfolding of A_Strlen.p_valid_str for the havoced memory a_3.

(defun-sk srg4-a3-chars-sint8-through-p
    (a1 length address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (srg4-is-sint8-p
       (srg4-a3-read
        (srg4-shift address position)
        a1 length))))))

(defun-sk srg4-a3-valid-string-p
    (a1 length address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (srg4-a3-read
       (srg4-shift address index)
       a1 length)
      0)
     (srg4-is-uint64-p index)
     (srg4-valid-rw-p
      (srg4-shift address 0)
      (+ 1 index))
     (srg4-a3-chars-sint8-through-p
      a1 length address index))))

;; Exact unfolding of A_Strlen.p_valid_str for the arbitrary next memory t_3.

(defun-sk srg4-t3-chars-sint8-through-p
    (address bound)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= position bound)
      (srg4-is-sint8-p
       (srg4-t3
        (srg4-shift address position)))))))

(defun-sk srg4-t3-valid-string-p (address)
  (exists (index)
    (and
     (integerp index)
     (equal
      (srg4-t3
       (srg4-shift address index))
      0)
     (srg4-is-uint64-p index)
     (srg4-valid-rw-p
      (srg4-shift address 0)
      (+ 1 index))
     (srg4-t3-chars-sint8-through-p
      address index))))

;; Universal closures of A_Strlen.fix_l_strlen and Q_TL_strlen for t_2.

(defun-sk srg4-t2-strlen-laws-p ()
  (forall (address)
    (implies
     (srg4-address-p address)
     (and
      (if
          (equal
           (srg4-t2
            (srg4-shift address 0))
           0)
          (equal
           (srg4-l-strlen-t2 address)
           0)
        (equal
         (srg4-to-uint64
          (+ 1
             (srg4-l-strlen-t2
              (srg4-shift address 1))))
         (srg4-l-strlen-t2 address)))
      (srg4-is-uint64-p
       (srg4-l-strlen-t2 address))))))

;; Exact extensional rendering of
;; if a_4 = i then Function.update a_3 a i_1 = t_3 else a_3 = t_3.

(defun-sk srg4-next-memory-equality-p
    (a1 length current current-value old-value replacement)
  (forall (address)
    (implies
     (srg4-address-p address)
     (equal
      (srg4-t3 address)
      (if (equal current-value old-value)
          (if (equal address current)
              replacement
            (srg4-a3-read address a1 length))
        (srg4-a3-read address a1 length))))))

;; The four loop-invariant hypotheses retain their internal quantifiers over
;; every mathematical integer or every source address.

(defun-sk srg4-no-null-before-length-p
    (a1 length)
  (forall (position)
    (implies
     (integerp position)
     (implies
      (<= 0 position)
      (implies
       (< position length)
       (not
        (equal
         (srg4-t2
          (srg4-shift a1 position))
         0)))))))

(defun-sk srg4-a3-equals-t2-in-range-p
    (a1 length current endpoint)
  (forall (candidate)
    (implies
     (srg4-address-p candidate)
     (implies
      (srg4-addr-le-p current candidate)
      (implies
       (srg4-addr-lt-p candidate endpoint)
       (equal
        (srg4-a3-read candidate a1 length)
        (srg4-t2 candidate)))))))

(defun-sk srg4-replaced-before-current-p
    (a1 length current old-value replacement)
  (forall (candidate)
    (implies
     (srg4-address-p candidate)
     (implies
      (equal
       (srg4-t2 candidate)
       old-value)
      (implies
       (srg4-addr-lt-p candidate current)
       (implies
        (srg4-addr-le-p a1 candidate)
        (equal
         (srg4-a3-read candidate a1 length)
         replacement)))))))

(defun-sk srg4-unchanged-before-current-p
    (a1 length current old-value)
  (forall (candidate)
    (implies
     (srg4-address-p candidate)
     (let
         ((source-value
           (srg4-t2 candidate)))
       (implies
        (not
         (equal source-value old-value))
        (implies
         (srg4-addr-lt-p candidate current)
         (implies
          (srg4-addr-le-p a1 candidate)
          (equal
           (srg4-a3-read candidate a1 length)
           source-value))))))))

(defun-sk
    ntp4vc-strreplace-loop-inv-preserved-goal4-statement ()
  (forall
   (a1 a i i1)
   (implies
    (and
     (srg4-address-p a1)
     (srg4-address-p a)
     (integerp i)
     (integerp i1)
     (srg4-function-types-p)
     (srg4-address-order-laws-p)
     (srg4-to-uint64-laws-p)
     (srg4-t2-strlen-laws-p))
    (let*
        ((length
          (srg4-l-strlen-t2 a1))
         (endpoint
          (srg4-shift a1 length))
         (current-value
          (srg4-a3-read a a1 length)))
      (implies
       (and
        (equal
         (srg4-t2 endpoint)
         0)
        (not
         (equal current-value 0))
        (<=
         (srg4-region
          (srg4-address-base a1))
         0)
        (srg4-linked-p)
        (srg4-sconst-p)
        (srg4-is-sint8-p i)
        (srg4-is-sint8-p i1)
        (srg4-addr-le-p a1 a)
        (srg4-t2-valid-string-p a1)
        (srg4-is-uint64-p length)
        (srg4-addr-le-p a endpoint)
        (srg4-is-sint8-p current-value)
        (srg4-a3-valid-string-p
         a1 length a)
        (srg4-a3-valid-string-p
         a1 length a1)
        (srg4-next-memory-equality-p
         a1 length a current-value i i1)
        (srg4-no-null-before-length-p
         a1 length)
        (srg4-a3-equals-t2-in-range-p
         a1 length a endpoint)
        (srg4-replaced-before-current-p
         a1 length a i i1)
        (srg4-unchanged-before-current-p
         a1 length a i))
       (srg4-t3-valid-string-p
        (srg4-shift a 1)))))))

(value-triple :itpeval-statement-checked)

:q
