;; Statement-only formalization of the NTP4VC corpus artifact
;; pearl/multiprecision/powm_Powm_win_sizeqtvc: the verification condition for
;; selecting a bounded positive sliding-window size from a signed 32-bit
;; exponent bit count. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Canonical integers in [0, 2^32) represent source 32-bit words exactly.

(defun winsz-bv32-p (word)
  (and
   (integerp word)
   (<= 0 word)
   (< word 4294967296)))

(defun winsz-sint32 (word)
  (if (< word 2147483648)
      word
    (- word 4294967296)))

;; This is the nested conditional defining the Why3 win_size result.

(defun winsz-selected-result (eb o1)
  (if (equal o1 t)
      0
    (if (<= (winsz-sint32 eb) 7)
        1
      (if (<= (winsz-sint32 eb) 25)
          2
        (if (<= (winsz-sint32 eb) 81)
            3
          (if (<= (winsz-sint32 eb) 214)
              4
            (if (<= (winsz-sint32 eb) 673)
                5
              (if (<= (winsz-sint32 eb) 1793)
                  6
                (if (<= (winsz-sint32 eb) 4609)
                    7
                  (if (<= (winsz-sint32 eb) 11521)
                      8
                    (if (<= (winsz-sint32 eb) 28161)
                        9
                      10)))))))))))

(defun
    ntp4vc-pearl-multiprecision-powm-powm-win-sizeqtvc-statement
    (eb o1 result)
  (implies
   (and
    (winsz-bv32-p eb)
    (booleanp o1)
    (winsz-bv32-p result)
    (implies
     (equal (winsz-sint32 eb) 0)
     (equal o1 t))
    (implies
     (equal o1 t)
     (equal eb 0))
    (equal result
           (winsz-selected-result eb o1)))
   (and
    (<= 0 (winsz-sint32 result))
    (<= (winsz-sint32 result) 10)
    (implies
     (< 0 (winsz-sint32 eb))
     (< 0 (winsz-sint32 result))))))

(set-inhibit-output-lst nil)
(value-triple :itpeval-statement-checked)
:q
