
a = [[1,3,4,5],
    [1,1,1,2],
    [2,0,3,4],   
    [1,3,4,1]]
max = 0
for i in range(0,3):
    for j in range(0,3):
        sum = a[i][j] + a[i][j+1] + a[i+1][j] + a[i+1][j+1]
        if max < sum : max = sum     
        
print('Tong diem lon nhat la \t' + str(max))



