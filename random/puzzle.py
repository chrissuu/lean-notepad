"""
Author: Chris Su
Date: Oct 7, 2025
Program Name: Puzzle Solution for math.inc

Suppose that today is June 1, 2025. We call a date "square" if all of its components
(day, month, and year) are perfect squares. I was born in the last millennium,
and my next birthday (relative to that date) will be the last square date in my
life. If you sum the square roots of the components of that upcoming square birthday
(day, month, year), you obtain my age on June 1, 2025. My mother would have been born
on a square date if the month were a square number; in reality it is not a square date,
but both the month and day are perfect cubes. When was I born, and when was my mother born?
"""

# 6 / 1 / 2025
# Born 1000 - 2000
# Life is 120 years
# So looking for a square date within 75 years after 2025
# age = 2025 - (day+month+year)
# mother would've been born on a square date if the month were a square number. 
# day is a square number and also a perfect cube? 
# month is a cube number but not a square number
# day = k ** 2 and also k ** 3
# for 1 <= day <= 31

# So next birthdate is on 2025, month is 9, (September), date is 25?
# So born on 9/25
# meaning age is 3 + 5 + 45 = 53

# mother's birth year: 1936
# month: 8 = 2 * 2 * 2 OR 1 = 1 * 1 * 1 OR 
# day: 8 OR 1 but 1 is square so has to be 1
# month should be 8 since not a square number

# My birthdate: 9 / 25 / 1972
# Mother's birthdate: 8 / 1 / 1936