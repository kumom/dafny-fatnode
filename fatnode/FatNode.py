from typing import Any
from functools import reduce

class Entry:
    def __init__(self):
        self.roots: list[Node] = [None]
        self.time = 0

    def __str__(self):
        return "~~~~~~~~~~~\n" + " | ".join(map(lambda r: " ".join(map(lambda v: f't{v[0]}: {v[1]}', r.values)) if r else "None", self.roots)) + "\n~~~~~~~~~~~"

    def get(self, version):
        if len(self.roots) > version:
            return self.roots[version]
        else:
            return self.roots[-1]

    def insert(self, value):
        self.time += 1
        root = self.roots[-1]
        if root is None:
            self.roots += [Node(value, self.time)]
        else:
            inserted = root.insert(value, self.time)
            self.roots += [root]

    def delete(self, value):
        root = self.roots[-1]
        if root:
            self.time += 1
            newRoot = root.delete(None, -1, value, self.time)
            self.roots += [newRoot]
        else:
            self.roots += [root]

    def find(self, version, value):
        if len(self.roots) > version:
            root = self.roots[version]
        else:
            root = self.roots[-1]

        if root:
            return root.find(version, value)
        else:
            return False

class Node:
    def __init__(self, value: int, time: int):
        self.values: list[tuple[int, int]] = [(time, value)]
        self.lefts: list[tuple[int, Any]] = []
        self.rights: list[tuple[int, Any]] = []

    def __str__(self, level=0):
        indent = "   " * level
        
        string = indent + "[" + " ".join(map(lambda t: f't{t[0]}: {t[1]}', self.values)) + "]"
        for p in self.rights:
            string += f'\n{indent}-r{p[0]}->\n'
            if p[1]:
                string += p[1].__str__(level + 1)
            else:
                indentt = "   " * (level + 1)
                string += f"{indentt}None"
        for p in self.lefts:
            string += f'\n{indent}-l{p[0]}->\n'
            if p[1]:
                string += p[1].__str__(level + 1)
            else:
                indentt = "   " * (level + 1)
                string += f"{indentt}None"
        return string

    def left(self):
        if len(self.lefts) > 0:
            return self.lefts[-1][1]
        else:
            return None

    def right(self):
        if len(self.rights) > 0:
            return self.rights[-1][1]
        else:
            return None

    def value(self):
        return self.values[-1][1]

    def versionsOnly(self, arr):
        return map(lambda t: t[0], arr)

    def insert(self, value, time) -> bool:
        x = self.value()
        if x < value:
            right = self.right()
            if right is None:
                self.rights += [(time, Node(value, time))]
                return True
            else:
                return right.insert(value, time)
        elif x > value:
            left = self.left()
            if left is None:
                self.lefts += [(time, Node(value, time))]
                return True
            else:
                return left.insert(value,  time)

        return False
    
    def deleteMin(self, parent: Any, direction: int, time: int):
        left = self.left()
        if left is None:
            if direction == 0:
                parent.lefts += [(time, self.right())]
            elif direction == 1:
                parent.rights += [(time, self.right())]
            return self.value()
        else:
            return left.deleteMin(self, 0, time)

    def delete(self, parent: Any, direction: int, value: int, time: int) -> Any:
        x = self.value()
        right = self.right()
        left = self.left()
        if x == value:
            if right:
                minV = right.deleteMin(self, 1, time)
                self.values += [(time, minV)]
            else:
                if parent is None:
                    return left
                else:
                    if direction == 0:
                        parent.lefts += [(time, left)]
                    elif direction == 1:
                        parent.rights += [(time, left)]

        elif x < value:
            if right:
                right.delete(self, 1, value, time)
        else:
            if left:
                left.delete(self, 0, value, time)

        return self

    def binarySearch(self, version: int, versionList: list[int]) -> int:
        if len(versionList) == 0 or version < versionList[0]:
            return -1

        lo, hi = 0, len(versionList) - 1
        i = 0
        while lo <= hi:
            mid = lo + (hi - lo) // 2
            v = versionList[mid]
            if version >= v:
                i = mid
                lo = mid + 1
                if version == v:
                    break
            else:
                hi = mid - 1

        return i

    def findHelper(self, version: int, fieldName: str) -> Any:
        if (fieldName == "value"):
            i = self.binarySearch(version, list(map(lambda t: t[0], self.values)))
            return self.values[i][1] if i >= 0 else None
        elif (fieldName == "right"):
            i = self.binarySearch(version, list(map(lambda t: t[0], self.rights)))
            return self.rights[i][1] if i >= 0 else None
        elif (fieldName == "left"):
            i = self.binarySearch(version, list(map(lambda t: t[0], self.lefts)))
            return self.lefts[i][1] if i >= 0 else None
        else:
            return None

    def find(self, version: int, value: int):
        x = self.findHelper(version, 'value')
        if x:
            if x > value:
                left = self.findHelper(version, 'left')
                if left == None:
                    return False
                else:
                    return left.find(version, value)
            elif x < value:
                right = self.findHelper(version, 'right')
                if right == None:
                    return False
                else:
                    return right.find(version, value)
            else:
                return True
        else:
            return False

entry = Entry() 
entry.insert(1) #1
entry.delete(1) #2
entry.insert(3) #3
entry.insert(2) #4
entry.insert(5) #5
entry.insert(4) #6
entry.delete(3) #7
entry.insert(6) #8
entry.insert(7) #9

print(entry)
print(entry.get(11))

for i in range(0, 11):
    k = 3
    print(f'{k} existed at time {i}: ', entry.find(i, k))
