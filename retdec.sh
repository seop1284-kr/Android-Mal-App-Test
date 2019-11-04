#!/usr/bin/env bash
:<<'END'
Usage: test.sh <apk>
apk is  application name
END

pwd=`pwd`
filepath=`pwd`/$1
filename="$(basename $filepath .apk)"
temp=$pwd/temp/$filename
output=$pwd/output/$filename

declare -A symbols

ret=`7z l $filepath | grep '\.so'`
if [ -n "$ret" ]; then
    rm -rf $temp
    unzip $filepath -d $temp

    rm -rf $output
    mkdir $output

    if [[ -d $temp/lib/armeabi-v7a ]]; then
        /home/pllab/retdec/bin/retdec-decompiler.py  $temp/lib/armeabi-v7a/*.so -o $output/$filename --no-memory-limit
        sofile=$temp/lib/armeabi-v7a/*.so
    else
        /home/pllab/retdec/bin/retdec-decompiler.py  $temp/lib/armeabi/*.so -o $output/$filename
        sofile=$temp/lib/armeabi/*.so
    fi

    asm=`arm-linux-gnueabi-objdump -d $sofile`
    while read -r line; do
        if [[ "$line" =~ "@plt>" ]]; then
            if [[ `wc -w <<< $line` == 2 ]]; then
                str=($line)
                addr="${str[0]}"
                addr=$(echo $addr | sed 's/^0*//')
                name="${str[1]}"
                name=${name%%@*}
                name=${name#<}_plt
                echo $addr $name
                symbols[$addr]=$name
            fi
        elif [[ "$line" =~ "@@Base>" ]]; then
            if [[ `wc -w <<< $line` == 2 ]]; then
                str=($line)
                addr="${str[0]}"
                addr=$(echo $addr | sed 's/^0*//')
                name="${str[1]}"
                name=${name%%@*}
                name=${name#<}
                echo $addr $name
                symbols[$addr]=$name
            fi
        fi
    done <<< $asm

    while read -r line; do
        if [[ "$line" =~ "@function_" ]]; then
            addr=${line##*@function_}
            addr=${addr%%(*}
            if [[ -v "symbols['$addr']" ]]; then
                echo @function_$addr @${symbols["$addr"]}
                line=$(echo $line | sed "s/@function_$addr/@${symbols[$addr]}/")
            fi
            echo "$line" >> $output/out.ll
        else
            echo "$line" >> $output/out.ll
        fi
    done < $output/$filename.ll
else
    echo "no native application"
fi
