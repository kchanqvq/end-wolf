(uiop:define-package #:end-wolf
  (:use #:cl #:iterate #:alexandria))

(in-package #:end-wolf)

(declaim (type (simple-array (unsigned-byte 10) (18 4)) *binomial-table*)
         (inline encode-set decode-set
                 reencode-wolf-index decode-wolf-index max-wolf-index))

(deftype state () '(unsigned-byte 35))
(deftype board () '(unsigned-byte 25))
(deftype bitpos () '(unsigned-byte 5))

(sb-ext:defglobal *binomial-table*
    (let ((table (make-array '(18 4) :initial-element 0 :element-type '(unsigned-byte 10))))
      (loop for n from 0 to 17 do
        (setf (aref table n 0) 1)
        (loop for k from 1 to (min n 3) do
          (setf (aref table n k)
                (+ (aref table (1- n) (1- k))
                   (aref table (1- n) k)))))
      table))

(defun encode-set (a b c)
  (declare (optimize speed) (type (unsigned-byte 5) a b c))
  (+ a (aref *binomial-table* b 2) (aref *binomial-table* c 3)))

(defun decode-set (index)
  (declare (optimize speed) (type (unsigned-byte 10) index))
  (let* ((n3 (loop for n from 17 downto 0
                   if (<= (aref *binomial-table* n 3) index) return n))
         (rem3 (- index (aref *binomial-table* n3 3)))

         (n2 (loop for n from (1- n3) downto 0
                   if (<= (aref *binomial-table* n 2) rem3) return n))
         (rem2 (- rem3 (aref *binomial-table* n2 2)))

         (n1 (loop for n from (1- n2) downto 0
                   if (<= n rem2) return n)))
    (values n1 n2 n3)))

(defun reencode-wolf-index (mask state)
  (declare (optimize speed)
           (type board mask)
           (type state state))
  (let ((a 0) (b 0) (c 0))
    (declare (type bitpos a b c))
    (let* ((low-bit (logand mask (- mask)))
           (idx (logcount (logand state (1- low-bit)))))
      (setq a idx mask (logxor mask low-bit)))
    (let* ((low-bit (logand mask (- mask)))
           (idx (logcount (logand state (1- low-bit)))))
      (setq b idx mask (logxor mask low-bit)))
    (let* ((low-bit (logand mask (- mask)))
           (idx (logcount (logand state (1- low-bit)))))
      (setq c idx mask (logxor mask low-bit)))
    (setf (ldb (byte 10 25) state) (encode-set a b c))
    state))

(defun decode-wolf-index (state)
  (declare (optimize speed)
           (type state state))
  (multiple-value-bind (a b c) (decode-set (ldb (byte 10 25) state))
    (let ((mask 0) (count 0))
      (declare (type board mask)
               (type bitpos count))
      (flet ((find-next (target)
               (loop while (< count target) do
                 (setf state (logand state (1- state))) ; Clear lowest bit
                 (incf count))
               (let ((low-bit (logand state (- state))))
                 (setf mask (logior mask low-bit)))))
        (find-next a)
        (find-next b)
        (find-next c)
        mask))))

;; inclusive
(defun max-wolf-index (max-n-pieces)
  (encode-set (- max-n-pieces 3) (- max-n-pieces 2) (- max-n-pieces 1)))

(defun encode-state (list)
  (let ((state 0)
        (logcount 0)
        (ws nil)
        (i 0))
    (dolist (row list)
      (dolist (piece row)
        (ecase piece
          (w (push logcount ws)
           (setf (ldb (byte 1 i) state) 1)
           (incf logcount))
          (s (setf (ldb (byte 1 i) state) 1)
           (incf logcount))
          (-))
        (incf i)))
    (setf (ldb (byte 10 25) state) (apply #'encode-set (reverse ws)))
    state))

(defun decode-state (state)
  (let ((wm (decode-wolf-index state)))
    (iter (with bitpos = 0)
      (for i below 5)
      (collecting
        (iter (for j below 5)
          (if (plusp (ldb (byte 1 bitpos) state))
              (collect (if (plusp (ldb (byte 1 bitpos) wm))
                           'w 's))
              (collect '-))
          (incf bitpos))))))

(defun print-state (state)
  (format t "~{~{~a~^ ~}~%~}~%"(decode-state state)))

(defun fuzz-encode-decode (seed)
  (let ((*random-state* (sb-ext:seed-random-state seed)))
    (iter (with n = 0)
      (repeat 100000)
      (for wc = 0)
      (for sc = 0)
      (for state = (iter
                     (for i below 5)
                     (collecting
                       (iter (for j below 5)
                         (collecting
                           (case (random 5)
                             ((0 1) '-)
                             ((2 3) (if (< sc 15)
                                        (prog1 's (incf sc))
                                        '-))
                             (4 (if (< wc 3)
                                    (prog1 'w (incf wc))
                                    '-))))))))
      (unless (< wc 3)
        (incf n)
        (let ((encoded (encode-state state)))
          (unless (equal state (decode-state encoded))
            (error "state ~a" state))
          (unless (= encoded (reencode-wolf-index (decode-wolf-index encoded) encoded))
            (error "wolf index ~a" state))))
      (finally (return n)))))

(declaim (inline sheep-forward wolf-forward
                 sheep-backward wolf-move-backward))

(defun sheep-forward (state cont)
  (declare (optimize speed)
           (type state state)
           (type function cont))
  (let* ((wm (decode-wolf-index state))
         (sm (ldb (byte 25 0) (logxor wm state)))
         (em (ldb (byte 25 0) (lognot state))))
    (declare (type board wm sm em))
    (let* ((sm-right (ash sm 1))
           (sm-into (logand sm-right em #b1111011110111101111011110)))
      (loop while (plusp sm-into) do
        (let ((low-bit (logand sm-into (- sm-into))))
          (setf sm-into (logand sm-into (1- sm-into)))
          (funcall cont (logxor state low-bit (ash low-bit -1))))))
    (let* ((sm-left (ash sm -1))
           (sm-into (logand sm-left em #b0111101111011110111101111)))
      (loop while (plusp sm-into) do
        (let ((low-bit (logand sm-into (- sm-into))))
          (setf sm-into (logand sm-into (1- sm-into)))
          (funcall cont (logxor state low-bit (ash low-bit 1))))))
    (let* ((sm-down (ash sm 5))
           (sm-into (logand sm-down em #b1111111111111111111100000)))
      (loop while (plusp sm-into) do
        (let ((low-bit (logand sm-into (- sm-into))))
          (setf sm-into (logand sm-into (1- sm-into)))
          (funcall cont (reencode-wolf-index wm (logxor state low-bit (ash low-bit -5)))))))
    (let* ((sm-down (ash sm -5))
           (sm-into (logand sm-down em #b0000011111111111111111111)))
      (loop while (plusp sm-into) do
        (let ((low-bit (logand sm-into (- sm-into))))
          (setf sm-into (logand sm-into (1- sm-into)))
          (funcall cont (reencode-wolf-index wm (logxor state low-bit (ash low-bit 5)))))))))

(defun sheep-backward (state cont)
  (sheep-forward state cont))

(defun wolf-forward (state cont)
  (declare (optimize speed)
           (type state state)
           (type function cont))
  (let ((wm (decode-wolf-index state)))
    (macrolet ((consider-move (skip-move-reencode move-test move-pos cap-test cap-pos)
                 `(when ,move-test
                    (when (zerop (ldb (byte 1 ,move-pos) state))
                      (let ((new-state new-state))
                        (setf (ldb (byte 1 ,move-pos) new-state) 1)
                        ,(if skip-move-reencode
                             '(funcall cont new-state)
                             `(let ((new-wm new-wm))
                                (setf (ldb (byte 1 ,move-pos) new-wm) 1)
                                (funcall cont (reencode-wolf-index new-wm new-state)))))
                      (when ,cap-test
                        (when (and (plusp (ldb (byte 1 ,cap-pos) state))
                                   (zerop (ldb (byte 1 ,cap-pos) wm)))
                          (let ((new-wm new-wm))
                            (setf (ldb (byte 1 ,cap-pos) new-wm) 1)
                            (funcall cont (reencode-wolf-index new-wm new-state)))))))))
      (let ((next-wm wm))
        (iter (repeat 3)
          (let ((new-state state)
                (new-wm wm)
                (bitpos (1- (integer-length next-wm))))
            (declare (type bitpos bitpos))
            (setf (ldb (byte 1 bitpos) new-state) 0
                  (ldb (byte 1 bitpos) new-wm) 0
                  (ldb (byte 1 bitpos) next-wm) 0)
            (multiple-value-bind (i j) (floor bitpos 5)
              (consider-move t (> j 0) (- bitpos 1) (> j 1) (- bitpos 2))
              (consider-move t (< j 4) (+ bitpos 1) (< j 3) (+ bitpos 2))
              (consider-move nil (> i 0) (- bitpos 5) (> i 1) (- bitpos 10))
              (consider-move nil (< i 4) (+ bitpos 5) (< i 3) (+ bitpos 10)))))))))

(defun wolf-move-backward (state cont)
  (declare (optimize speed)
           (type state state)
           (type function cont))
  (let ((wm (decode-wolf-index state)))
    (macrolet ((consider-move (skip-move-reencode move-test move-pos)
                 `(when ,move-test
                    (when (zerop (ldb (byte 1 ,move-pos) state))
                      (let ((new-state new-state))
                        (setf (ldb (byte 1 ,move-pos) new-state) 1)
                        ,(if skip-move-reencode
                             '(funcall cont new-state)
                             `(let ((new-wm new-wm))
                                (setf (ldb (byte 1 ,move-pos) new-wm) 1)
                                (funcall cont (reencode-wolf-index new-wm new-state)))))))))
      (let ((next-wm wm))
        (iter (repeat 3)
          (let ((new-state state)
                (new-wm wm)
                (bitpos (1- (integer-length next-wm))))
            (declare (type bitpos bitpos))
            (setf (ldb (byte 1 bitpos) new-state) 0
                  (ldb (byte 1 bitpos) new-wm) 0
                  (ldb (byte 1 bitpos) next-wm) 0)
            (multiple-value-bind (i j) (floor bitpos 5)
              (consider-move t (> j 0) (- bitpos 1))
              (consider-move t (< j 4) (+ bitpos 1))
              (consider-move nil (> i 0) (- bitpos 5))
              (consider-move nil (< i 4) (+ bitpos 5)))))))))
